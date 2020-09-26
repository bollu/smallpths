{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedTuples #-}
module Main (main) where
import qualified Data.Vector as V
import qualified Data.Vector.Storable.Mutable as VM
import Data.List (find, minimumBy, foldl')
import Data.IORef
import Data.IORef.Unboxed
import Data.Word
import Text.Printf
import Foreign
import Foreign.C.Types
import System.IO (stderr, withFile, IOMode(..))
import GHC.Conc
import GHC.Prim
import GHC.Types hiding (SPEC)
import Control.Concurrent
import GHC.Float hiding (clamp)
-- position, also color (r,g,b)
data Vec = Vec {-# UNPACK #-} !Double {-# UNPACK #-} !Double {-# UNPACK #-} !Double

zerov = Vec 0 0 0
addv (Vec a b c) (Vec x y z) = Vec (a+x) (b+y) (c+z)
subv (Vec a b c) (Vec x y z) = Vec (a-x) (b-y) (c-z)
mulvs (Vec a b c) x = Vec (a*x) (b*x) (c*x)
mulv (Vec a b c) (Vec x y z) = Vec (a*x) (b*y) (c*z)
len (Vec a b c) = sqrt $ a*a+b*b+c*c
norm v = v `mulvs` (1/len v)
dot (Vec a b c) (Vec x y z) = a*x+b*y+c*z
cross (Vec a b c) (Vec x y z) = Vec (b*z-c*y) (c*x-a*z) (a*y-b*x)
maxv (Vec a b c) = max a (max b c)

data Ray = Ray {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec -- origin, direction

newtype Refl = Refl Int  -- material types, used in radiance

pattern DIFF = Refl 0
pattern SPEC = Refl 1
pattern REFR = Refl 2

-- radius, position, emission, color, reflection
data Sphere = Sphere {-# UNPACK #-} !Double {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec {-# UNPACK #-} !Refl

intersect !(Ray o d) !(Sphere r p e c refl) =
  if det<0 then (1/0.0) else f (b-sdet) (b+sdet)
  where !op = p `subv` o
        {-# INLINE op #-}
        !eps = 1e-4
        {-# INLINE eps #-}
        !b = op `dot` d
        {-# INLINE b #-}
        !det = b*b - (op `dot` op) + r*r
        {-# INLINE det #-}
        !sdet = sqrt det
        {-# INLINE sdet #-}
        f !a !b = if a>eps then a else if b>eps then b else (1/0.0)
        {-# INLINE f #-}
{-# INLINE intersect #-}

clamp x = if x<0 then 0 else if x>1 then 1 else x

toInt :: Double -> Int
toInt x = floor $ clamp x ** (1/2.2) * 255 + 0.5

intersects ray = 
    f (f (f (f (f (f (f (f (# intersect ray sphLeft, sphLeft #) sphRight) sphBack) sphFrnt) sphBotm) sphTop) sphMirr) sphGlas) sphLite
  where
    f !(# !k,!sp #) !s =
      let x = intersect ray s in if x < k then (# x,s #)  else (# k,sp #)

sphLeft  = Sphere 1e5  (Vec (1e5+1) 40.8 81.6)    zerov (Vec 0.75 0.25 0.25) DIFF --Left
sphRight = Sphere 1e5  (Vec (-1e5+99) 40.8 81.6)  zerov (Vec 0.25 0.25 0.75) DIFF --Rght
sphBack  = Sphere 1e5  (Vec 50 40.8 1e5)          zerov (Vec 0.75 0.75 0.75) DIFF --Back
sphFrnt  = Sphere 1e5  (Vec 50 40.8 (-1e5+170))   zerov zerov              DIFF --Frnt
sphBotm  = Sphere 1e5  (Vec 50 1e5 81.6)          zerov (Vec 0.75 0.75 0.75) DIFF --Botm
sphTop   = Sphere 1e5  (Vec 50 (-1e5+81.6) 81.6)  zerov (Vec 0.75 0.75 0.75) DIFF --Top
sphMirr  = Sphere 16.5 (Vec 27 16.5 47)           zerov (Vec 0.999 0.999 0.999) SPEC --Mirr
sphGlas  = Sphere 16.5 (Vec 73 16.5 78)           zerov (Vec 0.999 0.999 0.999) REFR --Glas
sphLite  = Sphere 600  (Vec 50 (681.6-0.27) 81.6) (Vec 12 12 12)       zerov DIFF --Lite

radiance :: Ray -> CInt -> IORefU Word -> IO Vec
radiance ray@(Ray o d) depth xi = case intersects ray of
  (# !t, _ #) | t == (1/0.0) -> return zerov
  (# !t, !Sphere r p e c refl #) -> do
    let !x = o `addv` (d `mulvs` t)
        !n = norm $ x `subv` p
        !nl = if n `dot` d < 0 then n else n `mulvs` (-1)
        !pr = maxv c
        !depth' = depth + 1
        continue !f = case refl of
          DIFF -> do
            !r1 <- ((2*pi)*) `fmap` erand48 xi
            !r2 <- erand48 xi
            let !r2s = sqrt r2
                !w@(Vec !wx _ _) = nl
                !u = norm $ (if abs wx > 0.1 then (Vec 0 1 0) else (Vec 1 0 0)) `cross` w
                !v = w `cross` u
                !d' = norm $ (u`mulvs`(cos r1*r2s)) `addv` (v`mulvs`(sin r1*r2s)) `addv` (w`mulvs`sqrt (1-r2))
            !rad <- radiance (Ray x d') depth' xi
            return $ e `addv` (f `mulv` rad)

          SPEC -> do
            let !d' = d `subv` (n `mulvs` (2 * (n`dot`d)))
            !rad <- radiance (Ray x d') depth' xi
            return $ e `addv` (f `mulv` rad)

          REFR -> do
            let !reflRay = Ray x (d `subv` (n `mulvs` (2* n`dot`d))) -- Ideal dielectric REFRACTION
                !into = n`dot`nl > 0                -- Ray from outside going in?
                !nc = 1
                !nt = 1.5
                !nnt = if into then nc/nt else nt/nc
                !ddn= d`dot`nl
                !cos2t = 1-nnt*nnt*(1-ddn*ddn)
            if cos2t<0    -- Total internal reflection
              then do
                !rad <- radiance reflRay depth' xi
                return $ e `addv` (f `mulv` rad)
              else do
                let !tdir = norm $ (d`mulvs`nnt `subv` (n`mulvs`((if into then 1 else -1)*(ddn*nnt+sqrt cos2t))))
                    !a=nt-nc
                    !b=nt+nc
                    !r0=a*a/(b*b)
                    !c = 1-(if into then -ddn else tdir`dot`n)
                    !re=r0+(1-r0)*c*c*c*c*c
                    !tr=1-re
                    !pp=0.25+0.5*re
                    !rp=re/pp
                    !tp=tr/(1-pp)
                !rad <-
                  if depth>2
                    then do !er <- erand48 xi
                            if er<pp -- Russian roulette
                              then (`mulvs` rp) `fmap` radiance reflRay depth' xi
                              else (`mulvs` tp) `fmap` radiance (Ray x tdir) depth' xi
                    else do !rad0 <- (`mulvs` re) `fmap` radiance reflRay depth' xi
                            !rad1 <- (`mulvs` tr) `fmap` radiance(Ray x tdir) depth' xi
                            return $ rad0 `addv` rad1
                return $ e `addv` (f `mulv` rad)

    if depth'>5
      then do
        !er <- erand48 xi
        if er < pr then continue $ c `mulvs` (1/pr)
                  else return e
      else continue c

smallpt :: Int -> Int -> Int -> IO ()
smallpt w h nsamps = do
  let samps = nsamps `div` 4
      org = Vec 50 52 295.6
      dir = norm $ Vec 0 (-0.042612) (-1)
      cx = Vec (fromIntegral w * 0.5135 / fromIntegral h) 0 0
      cy = norm (cx `cross` dir) `mulvs` 0.5135
  c <- VM.replicate (w * h) zerov
  xi <- newIORefU 0
  flip mapM_ [0..h-1] $ \y -> do
        --hPrintf stderr "\rRendering (%d spp) %5.2f%%" (samps*4::Int) (100.0*fromIntegral y/(fromIntegral h-1)::Double)
   writeXi xi y
   flip mapM_ [0..w-1] $ \x -> do
        let i = (h-y-1) * w + x
        flip mapM_ [0..1] $ \sy -> do
          flip mapM_ [0..1] $ \sx -> do
            r <- newIORef zerov
            flip mapM_ [0..samps-1] $ \s -> do
              r1 <- (2*) `fmap` erand48 xi
              let dx = if r1<1 then sqrt r1-1 else 1-sqrt(2-r1)
              r2 <- (2*) `fmap` erand48 xi
              let dy = if r2<1 then sqrt r2-1 else 1-sqrt(2-r2)
                  d = (cx `mulvs` (((sx + 0.5 + dx)/2 + fromIntegral x)/fromIntegral w - 0.5)) `addv`
                      (cy `mulvs` (((sy + 0.5 + dy)/2 + fromIntegral y)/fromIntegral h - 0.5)) `addv` dir
              rad <- radiance (Ray (org`addv`(d`mulvs`140)) (norm d)) 0 xi
              -- Camera rays are pushed forward ^^^^^ to start in interior
              modifyIORef r (`addv` (rad `mulvs` (1 / fromIntegral samps)))
            ci <- VM.unsafeRead c i
            Vec rr rg rb <- readIORef r
            VM.unsafeWrite c i $ ci `addv` (Vec (clamp rr) (clamp rg) (clamp rb) `mulvs` 0.25)

  withFile "image.ppm" WriteMode $ \hdl -> do
        hPrintf hdl "P3\n%d %d\n%d\n" w h (255::Int)
        flip mapM_ [0..w*h-1] $ \i -> do
          Vec r g b <- VM.unsafeRead c i
          hPrintf hdl "%d %d %d " (toInt r) (toInt g) (toInt b)

writeXi :: IORefU Word -> Int -> IO ()
writeXi !xi !(I# y) = writeIORefU xi (W# (mkErand48Seed# y))
{-# INLINE writeXi #-}

mkErand48Seed# :: Int# -> Word#
mkErand48Seed# y = 
  let yw = int2Word# y; prod = (yw `timesWord#` yw `timesWord#` yw)
  in concatWord# 0## 0## prod
{-# INLINE mkErand48Seed# #-}

mkErand48Seed :: Int -> IO (IORefU Word)
mkErand48Seed !(I# i) = newIORefU (W# (mkErand48Seed# i))
{-# INLINE mkErand48Seed #-}

concatWord# :: Word# -> Word# -> Word# -> Word#
concatWord# x0 x1 x2 = x0 `or#` (x1 `uncheckedShiftL#` 16#) `or#` (x2 `uncheckedShiftL#` 32#)
{-# INLINE concatWord# #-}

-- | returns the full state and the bitmasked value.
rand48_step# :: Word# -> (# Word#, Word# #)
rand48_step# x =
  let a = concatWord# lc0 lc1 lc2
      x' = (a `timesWord#` x) `plusWord#` lc3
      lc0 = 0xe66d##
      lc1 = 0xdeec##
      lc2 = 0x5##
      lc3 = 0xb##
  in (# x', x' `and#` 0xffffffffffff## #)
{-# INLINE rand48_step# #-}

erand48# :: Word# -> (# Word#, Double# #)
erand48# s =
  let (# s', out' #) = (rand48_step# s)
      d_word = (0x3ff0000000000000##) `or#`
               (out' `uncheckedShiftL#` 4#)
  in (# s' , (stgWord64ToDouble d_word) -## 1.0## #)
{-# INLINE erand48# #-}

erand48 :: IORefU Word -> IO Double
erand48 !t =  do
  (W# r) <- readIORefU t
  let (# r', d #) = erand48# r
  writeIORefU t (W# r')
  pure (D# d)
{-# INLINE erand48 #-}

instance Storable Vec where
  sizeOf _ = sizeOf (undefined :: Double) * 3
  alignment _ = alignment (undefined :: Double)
 
  {-# INLINE peek #-}
  peek p = do
             a <- peekElemOff q 0
             b <- peekElemOff q 1
             c <- peekElemOff q 2
             return (Vec a b c)
    where
    q = castPtr p

  {-# INLINE poke #-}
  poke p (Vec a b c) = do
             pokeElemOff q 0 a
             pokeElemOff q 1 b
             pokeElemOff q 2 c
    where
    q = castPtr p

main :: IO ()
main = smallpt 200 200 256
