{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnliftedNewtypes #-}
module Main where
import Control.Monad
import qualified Data.Vector as V
import qualified Data.Vector.Storable.Mutable as VM
import Data.List (find, minimumBy, foldl')
import Data.IORef
import Text.Printf
import Foreign
import Foreign.C.Types
import GHC.Base (isTrue#)
import GHC.Conc
import GHC.Float hiding (clamp)
import GHC.Prim
import GHC.Types (Bool(..), Double(..), Int(..), Word(..))
import System.IO (stderr, withFile, IOMode(..))
-- position, also color (r,g,b)
data Vec = Vec !Double# !Double# !Double#
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
data Sphere = Sphere !Double# {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec {-# UNPACK #-} !Vec !Refl

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

radiance :: Ray -> CInt -> TVar Word -> IO Vec
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
            (D# r) <- erand48 xi
            let r1 = (2.0## *## 3.141592653589793238##) *##  r
            (D# r2) <- erand48 xi
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
                    then do (D# er) <- erand48 xi
                            if isTrue# (er<##pp) -- Russian roulette
                              then (`mulvs` rp) `fmap` radiance reflRay depth' xi
                              else (`mulvs` tp) `fmap` radiance (Ray x tdir) depth' xi
                    else do rad0 <- (`mulvs` re) `fmap` radiance reflRay depth' xi
                            rad1 <- (`mulvs` tr) `fmap` radiance(Ray x tdir) depth' xi
                            return $ rad0 `addv` rad1
                return $ e `addv` (f `mulv` rad)

    if depth'>5
      then do
        (D# er) <- erand48 xi
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
  xi <- newTVarIO 0
  flip mapM_ [0..(I# (h-#1#))] $ \(I# y) -> do
      atomically $ writeTVar xi (W# (int2Word# y))
      flip mapM_ [0..(I# (w-#1#))] $ \(I# x) -> do
        let i = (h-#y-#1#) *# w +# x
        flip mapM_ [0..1] $ \(D# sy) -> do
          (\func -> foldM_ func zerov [0..1]) $ \r (D# sx) -> do
            r' <- (\funcin -> foldM funcin r [0..(I# (samps-#1#))]) $ \rin s -> do
              (D# r1) <- (2*) `fmap` erand48 xi
              let dx = if isTrue# (r1<## 1.0##) then sqrtDouble# r1-##1.0## else 1.0## -## sqrtDouble# (2.0## -## r1)
              (D# r2) <- (2*) `fmap` erand48 xi
              let dy = if isTrue# (r2<##1.0##) then sqrtDouble# r2-##1.0## else 1.0## -## sqrtDouble# (2.0## -## r2)
                  d = (cx `mulvs` (((sx +## 0.5## +## dx)/##2.0## +## int2Double# x)/##(int2Double# w) -## 0.5##)) `addv`
                      (cy `mulvs` (((sy +## 0.5## +## dy)/##2.0## +## int2Double# y)/##(int2Double# h) -## 0.5##)) `addv` dir
              rad <- radiance (Ray (org`addv`(d`mulvs`140.0##)) (norm d)) 0 xi
              -- Camera rays are pushed forward ^^^^^ to start in interior
              pure $ addv rin (rad `mulvs` (1.0## /## int2Double# samps))
            ci <- VM.unsafeRead c (I# i)
            let (Vec rr rg rb) = r'
            VM.unsafeWrite c (I# i) (ci `addv` (Vec (clamp rr) (clamp rg) (clamp rb) `mulvs` 0.25##))
            pure r'

  withFile "image-storable.ppm" WriteMode $ \hdl -> do
        hPrintf hdl "P3\n%d %d\n%d\n" (I# w) (I# h) (255::Int)
        flip mapM_ [0..(I# (w*#h-#1#))] $ \i -> do
          Vec r g b <- VM.unsafeRead c i
          hPrintf hdl "%d %d %d " (I# (toInt r)) (I# (toInt  g)) (I# (toInt b))


{-
double erand48(unsigned short s[3])
{
	union {
		uint64_t u;
		double f;
	} x = { 0x3ff0000000000000ULL | __rand48_step(s, __seed48+3)<<4 };
	return x.f - 1.0;
}
double drand48(void){ return erand48(__seed48); }

uint64_t __rand48_step(unsigned short *xi, unsigned short *lc)
{
	uint64_t a, x;
	x = xi[0] | xi[1]+0U<<16 | xi[2]+0ULL<<32;
	a = lc[0] | lc[1]+0U<<16 | lc[2]+0ULL<<32;
	x = a*x + lc[3];
	xi[0] = x;
	xi[1] = x>>16;
	xi[2] = x>>32;
	return x & 0xffffffffffffull;
}

https://github.com/ontio/musl-mirror/blob/7e1c4df4b2f14ab9d156439e9a596ca152c6f50f/src/prng/__seed48.c

unsigned short __seed48[7] = { 0, 0, 0, 0xe66d, 0xdeec, 0x5, 0xb };

-}


word2Double# :: Word# -> Double#; word2Double# = undefined
leftShiftWord# :: Word# -> Word#; leftShiftWord# = undefined
bitwiseOrWord# :: Word# -> Word#; bitwiseOrWord# = undefined

concatWord# :: Word# -> Word# -> Word# -> Word#
concatWord# x0 x1 x2 = x0 `or#` (x1 `uncheckedShiftL#` 16#) `or#` (x2 `uncheckedShiftL#` 32#)
rand48_step# :: Word# -> Word#
rand48_step# x =
  let a = concatWord# lc0 lc1 lc2
      x' = (a `timesWord#` x) `plusWord#` lc3
      lc0 = 0xe66d##
      lc1 = 0xdeec##
      lc2 = 0x5##; lc3 = 0xb##
  in x `and#` 0xffffffffffff##

erand48 :: TVar Word -> IO Double
erand48 t = atomically $ do
  (W# r) <- readTVar t
  let (# r', d #) = erand48# r
  writeTVar t (W# r')
  pure (D# d)

erand48# :: Word# -> (# Word#, Double# #)
erand48# i =
  let r = rand48_step# i
      d_word = (0x3ff0000000000000##) `or#` (r `uncheckedShiftL#` 4#)
      in (# i, stgWord64ToDouble d_word #)


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