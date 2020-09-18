{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnliftedNewtypes #-}
module Main where
import qualified Data.Vector as V
import qualified Data.Vector.Storable.Mutable as VM
import Data.List (find, minimumBy, foldl')
import Data.IORef
import Text.Printf
import Foreign
import Foreign.C.Types
import GHC.Base (isTrue#)
import GHC.Prim
import GHC.Types (Bool(..), Double(..), Int(..))
import System.IO (stderr, withFile, IOMode(..))
-- position, also color (r,g,b)
data Vec = Vec {-# UNPACK #-} !Double# {-# UNPACK #-} !Double# {-# UNPACK #-} !Double#
zerov = Vec 0.0## 0.0## 0.0##
addv (Vec a b c) (Vec x y z) = Vec (a+##x) (b+##y) (c+##z)
subv (Vec a b c) (Vec x y z) = Vec (a-##x) (b-##y) (c-##z)
mulvs (Vec a b c) x = Vec (a*##x) (b*##x) (c*##x)
mulv (Vec a b c) (Vec x y z) = Vec (a*##x) (b*##y) (c*##z)
len (Vec a b c) = sqrtDouble# (a*##a+##b*##b+##c*##c)
norm v = mulvs v (1.0##/##(len v))
dot (Vec a b c) (Vec x y z) = a*##x+##b*##y+##c*##z
cross (Vec a b c) (Vec x y z) = Vec (b*##z-##c*##y) (c*##x-##a*##z) (a*##y-##b*##x)
max2 a b = case (a <## b) of
             0# -> a
             _ -> b
maxv (Vec a b c) = max2 (max2 a b) c

data Ray = Ray {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec -- origin, direction

data Refl = DIFF | SPEC | REFR -- material types, used in radiance

-- radius, position, emission, color, reflection
data Sphere = Sphere {-# UNPACK #-} !Double# {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec {-# UNPACK #-} !Refl

type Maybe' a = (# (# #) | a #)

intersect (Ray o d) (Sphere r p e c refl) =
  case det<##(0.0##) of { 0# -> f (b-##sdet) (b+##sdet); _ -> Nothing }
  where op = subv p o
        (D# eps) = 1e-4
        b = dot op d
        det = b*##b -## (dot op op) +## r*##r
        sdet = sqrtDouble# det
        f a b = case a>##eps of { 0# -> case b>##eps of { 0# -> Nothing; _ ->  Just (D# b)}; _ -> Just (D# a)}

spheres =
  let s = Sphere
      z = zerov
      v = Vec
      (*) = mulvs
  in
  [ s 1e5##   (v (1e5##+##1.0##) 40.8## 81.6##)    z (v 0.75## 0.25## 0.25##) DIFF --Left
  , s 1e5##   (v (-1e5##+##99.0##) 40.8## 81.6##)  z (v 0.25## 0.25## 0.75##) DIFF --Rght
  , s 1e5##   (v 50.0## 40.8## 1e5##)          z (v 0.75## 0.75## 0.75##) DIFF --Back
  , s 1e5##   (v 50.0## 40.8## (-1e5##+##170.0##))   z z                  DIFF --Frnt
  , s 1e5##   (v 50.0## 1e5## 81.6##)          z (v 0.75## 0.75## 0.75##) DIFF --Botm
  , s 1e5##   (v 50.0## (-1e5##+##81.6##) 81.6##)  z (v 0.75## 0.75## 0.75##) DIFF --Top
  , s 16.5##  (v 27.0## 16.5## 47.0##)           z ((v 1.0## 1.0## 1.0##) * 0.999##) SPEC --Mirr
  , s 16.5##  (v 73.0## 16.5## 78.0##)           z ((v 1.0## 1.0## 1.0##) * 0.999##) REFR --Glas
  , s 600.0## (v 50.0## (681.6##-##0.27##) 81.6##) (v 12.0## 12.0## 12.0##)       z DIFF]--Lite

clamp x = case  x <## 0.0## of { 0# -> case  x >## 1.0## of { 0# -> x; _ ->  1.0## };  _ ->  0.0## }

toInt :: Double# -> Int#
toInt x =
  case double2Int# (clamp (x **## (1.0##/##2.2##) *## 255.0## +## 0.5##)) of
    n | isTrue# (x <## int2Double# n) -> (n -# 1#)
      | otherwise                     -> n

intersects ray = (k, s)
  where (k,s) = foldl' f (Nothing,undefined) spheres
        f (k,sp) s = case (k,intersect ray s) of
                  (Nothing,Just x) -> (Just x,s)
                  (Just y,Just x) | x < y -> (Just x,s)
                  _ -> (k,sp)

radiance :: Ray -> CInt -> Ptr CUShort -> IO Vec
radiance ray@(Ray o d) depth xi =
 case intersects ray of
  (Nothing,_) -> return zerov
  (Just (D# t),Sphere r p e c refl) -> do
    let x = addv o (mulvs d t)
        n = norm $ x `subv` p
        nl = if isTrue# ((dot n d) <## 0.0##) then n else mulvs n (-1.0##)
        pr = maxv c
        depth' = depth + 1
        continue f = case refl of
          DIFF -> do
            (CDouble (D# r)) <- erand48 xi
            let r1 = (2.0## *## 3.141592653589793238##) *##  r
            (CDouble (D# r2)) <- erand48 xi
            let r2s = sqrtDouble# r2
                w@(Vec wx _ _) = nl
                u = norm (cross (if isTrue# (fabsDouble# wx >## 0.1##) then (Vec 0.0## 1.0## 0.0##) else (Vec 1.0## 0.0## 0.0##)) w)
                v = w `cross` u
                d' = norm $ (u`mulvs`(cosDouble# r1*##r2s)) `addv` (v`mulvs`(sinDouble# r1*##r2s)) `addv` (w`mulvs`sqrtDouble# (1.0## -##r2))
            rad <- radiance (Ray x d') depth' xi
            return $ e `addv` (f `mulv` rad)

          SPEC -> do
            let d' = d `subv` (n `mulvs` (2.0## *## (n`dot`d)))
            rad <- radiance (Ray x d') depth' xi
            return $ e `addv` (f `mulv` rad)

          REFR -> do
            let reflRay = Ray x (d `subv` (n `mulvs` (2.0## *## n`dot`d))) -- Ideal dielectric REFRACTION
                into = n`dot`nl >## 0.0##                -- Ray from outside going in?
                nc = 1.0##
                nt = 1.5##
                nnt = if isTrue# into then nc/##nt else nt/##nc
                ddn= d`dot`nl
                cos2t = 1.0##-##nnt*##nnt*##(1.0## -##ddn*##ddn)
            if isTrue# (cos2t<##0.0##)    -- Total internal reflection
              then do
                rad <- radiance reflRay depth' xi
                return $ e `addv` (f `mulv` rad)
              else do
                let tdir = norm (d`mulvs`nnt `subv` (n`mulvs`((if isTrue# into then 1.0## else -1.0##)*##(ddn*##nnt+##sqrtDouble# cos2t))))
                    a=nt-##nc
                    b=nt+##nc
                    r0=a*##a/##(b*##b)
                    c = 1.0## -## (if isTrue# into then -1.0## *## ddn else tdir`dot`n)
                    re=r0 +## (1.0## -## r0) *## c *## c*## c *## c *## c 
                    tr=1.0## -## re
                    pp=0.25## +## 0.5## *## re
                    rp=re /## pp
                    tp=tr /## (1.0## -## pp)
                rad <-
                  if (depth > 2 )
                    then do (CDouble (D# er)) <- erand48 xi
                            if isTrue# (er<##pp) -- Russian roulette
                              then (`mulvs` rp) `fmap` radiance reflRay depth' xi
                              else (`mulvs` tp) `fmap` radiance (Ray x tdir) depth' xi
                    else do rad0 <- (`mulvs` re) `fmap` radiance reflRay depth' xi
                            rad1 <- (`mulvs` tr) `fmap` radiance(Ray x tdir) depth' xi
                            return $ rad0 `addv` rad1
                return $ e `addv` (f `mulv` rad)

    if depth'>5
      then do
        (CDouble (D# er)) <- erand48 xi
        if isTrue# (er <## pr) then continue $ c `mulvs` (1.0## /## pr)
                  else return e
      else continue c

smallpt :: Int -> Int -> Int -> IO ()
smallpt (I# w) (I# h) nsamps = do
  let (I# samps) = nsamps `div` 4
      org = Vec 50.0## 52.0## 295.6##
      dir = norm $ Vec 0.0## (-0.042612##) (-1.0##)
      cx = Vec (int2Double# w *## 0.5135## /## int2Double# h) 0.0## 0.0##
      cy = norm (cx `cross` dir) `mulvs` 0.5135##
  c <- VM.replicate ((I# w) * (I# h)) zerov
  allocaArray 3 $ \xi ->
	flip mapM_ [0..(I# (h-#1#))] $ \(I# y) -> do
	  --hPrintf stderr "\rRendering (%d spp) %5.2f%%" (samps*4::Int) (100.0*fromIntegral y/(fromIntegral h-1)::Double)
      writeXi xi y
      flip mapM_ [0..(I# (w-#1#))] $ \(I# x) -> do
        let i = (h-#y-#1#) *# w +# x
        flip mapM_ [0..1] $ \(D# sy) -> do
          flip mapM_ [0..1] $ \(D# sx) -> do
            r <- newIORef zerov
            flip mapM_ [0..(I# (samps-#1#))] $ \s -> do
              (CDouble (D# r1)) <- (2*) `fmap` erand48 xi
              let dx = if isTrue# (r1<## 1.0##) then sqrtDouble# r1-##1.0## else 1.0## -## sqrtDouble# (2.0## -## r1)
              (CDouble (D# r2)) <- (2*) `fmap` erand48 xi
              let dy = if isTrue# (r2<##1.0##) then sqrtDouble# r2-##1.0## else 1.0## -## sqrtDouble# (2.0## -## r2)
                  d = (cx `mulvs` (((sx +## 0.5## +## dx)/##2.0## +## int2Double# x)/##(int2Double# w) -## 0.5##)) `addv`
                      (cy `mulvs` (((sy +## 0.5## +## dy)/##2.0## +## int2Double# y)/##(int2Double# h) -## 0.5##)) `addv` dir
              rad <- radiance (Ray (org`addv`(d`mulvs`140.0##)) (norm d)) 0 xi
              -- Camera rays are pushed forward ^^^^^ to start in interior
              modifyIORef r (`addv` (rad `mulvs` (1.0## /## int2Double# samps)))
            ci <- VM.unsafeRead c (I# i)
            Vec rr rg rb <- readIORef r
            VM.unsafeWrite c (I# i) (ci `addv` (Vec (clamp rr) (clamp rg) (clamp rb) `mulvs` 0.25##))

  withFile "image-storable.ppm" WriteMode $ \hdl -> do
	hPrintf hdl "P3\n%d %d\n%d\n" (I# w) (I# h) (255::Int)
	flip mapM_ [0..(I# (w*#h-#1#))] $ \i -> do
	  Vec r g b <- VM.unsafeRead c i
	  hPrintf hdl "%d %d %d " (I# (toInt r)) (I# (toInt  g)) (I# (toInt b))

writeXi :: Ptr CUShort -> Int# -> IO ()
writeXi xi y = do
  let y' = fromIntegral (I# y)
  pokeElemOff xi 0 0
  pokeElemOff xi 1 0
  pokeElemOff xi 2 (y' * y' * y')

foreign import ccall unsafe "erand48"
  erand48 :: Ptr CUShort -> IO CDouble

-- erand48' :: Ptr CUShort -> IO Double#
-- erand48' = do (CDouble D# x) <- erand48; return x

instance Storable Vec where
  sizeOf _ = sizeOf (undefined :: CDouble) * 3
  alignment _ = alignment (undefined :: CDouble)
 
  {-# INLINE peek #-}
  peek p = do
             (CDouble (D# a)) <- peekElemOff q 0
             (CDouble (D# b)) <- peekElemOff q 1
             (CDouble (D# c)) <- peekElemOff q 2
             return (Vec a b c)
    where
    q = castPtr p

  {-# INLINE poke #-}
  poke p (Vec a b c) = do
             pokeElemOff q 0 (D# a)
             pokeElemOff q 1 (D# b)
             pokeElemOff q 2 (D# c)
    where
    q = castPtr p

main :: IO ()
main=smallpt 200 200 256