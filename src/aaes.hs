-----------------------------------------------------------------------------
-- |
-- Module  :  FMS
-- Copyright   :  (c) Ricardo Bonna
-- License     :  BSD-3
--
-- Maintainer  :  ricardobonna@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
--
-----------------------------------------------------------------------------

module FMS (
  inertialIntegrator, euler, a_out, v_out, p_out, nzBody
  ) where

import ForSyDe.Shallow
import Quaternion
import Data.Maybe
import Data.List

type Vec = (Float, Float, Float)
type ImuVal = (Vec, Vec)

-----------------------------------------------------------------
------------ Inertial integrator as fixed procedure -------------
-----------------------------------------------------------------

integrator :: (Fractional a) => Rational -> a -> Signal a -> Signal a
integrator ts x0 u = out
  where out = comb2SY (+) trap (delaySY x0 out)
        trap = combSY (* t2) (comb2SY (+) u (delaySY (fromRational 0) u))
        t2 = fromRational ts / fromRational 2

quatIntegrator :: (RealFloat a) => Rational -> Quaternion a
               -> Signal (Quaternion a) -> Signal (Quaternion a)
quatIntegrator ts q_init w_q = q_k
  where q_k = comb2SY (\w q -> q * expQ (w * t2)) w_q (delaySY q_init q_k)
        t2 = fromRational ts / fromRational 2

voter :: (RealFloat a, Ord a) => a -> Quaternion a -> Quaternion a -> Quaternion a
      -> Quaternion a -> Quaternion a
voter ths q0 q1 q2 qx
  | qmax < ths = qm
  | normQ (head ql1 - last ql1) < 2*ths = divQR (head ql1 + last ql1) 2
  | otherwise = if head qnxl <= last qnxl then divQR (head ql1 + qx) 2 else divQR (last ql1 + qx) 2
  where ql = [q0, q1, q2]
        qm = divQR (q0+q1+q2) 3
        qnl = [normQ (q0-qm), normQ (q1-qm), normQ (q2-qm)]
        qmax = maximum qnl
        qmaxPos = fromJust (elemIndex qmax qnl)
        ql1 = take qmaxPos ql ++ drop (qmaxPos+1) ql
        qnxl = map (\q -> normQ (q-qx)) ql1

voterProc :: (RealFloat a, Ord a) => a -> Quaternion a -> Signal (Quaternion a) -> Signal (Quaternion a)
      -> Signal (Quaternion a) -> Signal (Quaternion a)
voterProc ths q0 s0 s1 s2 = sk
  where sk = comb4SY (voter ths) s0 s1 s2 (delaySY q0 sk)

accLocal2Inertial :: RealFloat a => Signal (Quaternion a) -> Signal (Quaternion a)
                  -> Signal (Quaternion a)
accLocal2Inertial = comb2SY (\q a_v -> rotQ q a_v - from3tupleQ (0, 0, 9.81))

tuple2quat :: (Num a) => Signal (a, a, a) -> Signal (Quaternion a)
tuple2quat = combSY from3tupleQ

inertialIntegrator :: Rational -> Float -> Float -> ImuVal -> Signal ImuVal -> Signal ImuVal
                   -> Signal ImuVal -> (Signal Vec, Signal Vec, Signal Vec, Signal Vec, Signal Float)
inertialIntegrator ts ths_w ths_a (w_init, a_init) imu0 imu1 imu2 = out
  where (w0, a0) = unzipSY imu0
        (w1, a1) = unzipSY imu1
        (w2, a2) = unzipSY imu2
        w_v = voterProc ths_w (from3tupleQ w_init) (tuple2quat w0) (tuple2quat w1) (tuple2quat w2)
        a_v = voterProc ths_a (from3tupleQ a_init) (tuple2quat a0) (tuple2quat a1) (tuple2quat a2)
        q = quatIntegrator ts (euler2quat (0, 0, 0)) w_v
        a = accLocal2Inertial q a_v
        v = integrator ts 0 a
        p = integrator ts 0 v
        euler = combSY quat2euler q
        nzBody = combSY (\acc -> (quat2list acc !! 3)/9.81) a_v
        a_out = combSY imagQ a
        v_out = combSY imagQ v
        p_out = combSY imagQ p
        out = (euler, a_out, v_out, p_out, nzBody)

----------- tests -----------

constant :: a -> Signal a
constant x = x :- constant x

imuInp = signal (replicate 10 ((0,0,1), (0,0,9.81)))
imuInpWrong = signal (replicate 5 ((0,0,1000), (0,0,981)))
imuInit = ((0,0,0),(0,0,0))
(euler, a_out, v_out, p_out, nzBody) = inertialIntegrator 0.01 1 1 imuInit imuInp imuInp imuInpWrong



-----------------------------------------------------------------
----------- Inertial integrator as variable procedure -----------
-----------------------------------------------------------------

rtrpFunc :: (Eq x) => AbstExt (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int) -> AbstExt s_in
         -> AbstExt x -> (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int, AbstExt x)
         -> ((AbstExt y, AbstExt x), (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int, AbstExt x))
rtrpFunc ctk s_ink x'k (fk,gk,mk,xk) = ((yk, xk1), (fk1,gk1,mk1,xk1))
  where yk = ykFunc ctk s_ink x'k gk mk xk
        (fk1,gk1,mk1,xk1) = nStateF ctk s_ink x'k (fk,gk,mk,xk)


nStateF :: (Eq x) => AbstExt (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int)
        -> AbstExt s_in
        -> AbstExt x
        -> (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int, AbstExt x)
        -> (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int, AbstExt x)
nStateF Abst s_ink x'k (fk,gk,mk,xk)
    | mk > 0 = (fk, gk, mk-1, Abst)
    | xk == Abst = (fk, gk, 0, fk x'k s_ink)
    | otherwise = (fk, gk, 0, fk xk s_ink)
nStateF (Prst (f,g,m)) _ _ _ = (f, g, m-1, Abst)


ykFunc :: (Eq x) => AbstExt (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int)
       -> AbstExt s_in
       -> AbstExt x
       -> (AbstExt x -> AbstExt s_in -> AbstExt y)
       -> Int
       -> AbstExt x
       -> AbstExt y
ykFunc Abst s_ink x'k gk mk xk
    | mk > 0 = Abst
    | xk == Abst = gk x'k s_ink
    | otherwise = gk xk s_ink
ykFunc _ _ _ _ _ _ = Abst


rtrp :: (Eq x, Eq y) => (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int, AbstExt x)  -- ^ Initial configuration
     -> Signal (AbstExt (AbstExt x -> AbstExt s_in -> AbstExt x, AbstExt x -> AbstExt s_in -> AbstExt y, Int))  -- ^ Control input
     -> Signal (AbstExt s_in)           -- ^ Signal input
     -> Signal (AbstExt x)              -- ^ Initial state input
     -> Signal (AbstExt y, AbstExt x)   -- ^ Output and state
rtrp (f0,g0,m0,x0) ct s_in x' = out
  where (out, fb) = unzipSY $ comb4SY rtrpFunc ct s_in x' fb'
        fb' = delaySY (f0,g0,m0,x0) fb


f :: Float  -- ^ Sampling period
  -> Float  -- ^ threshold for the voter of w
  -> Float  -- ^ threshold for the voter of a
  -> AbstExt [Quaternion Float] -- ^ Current state x[k] = [wv, av, q, a, v, p]
  -> AbstExt [ImuVal]   -- ^ List with the outputs from the three IMUs as pairs (w, a)
  -> AbstExt [Quaternion Float] -- ^ Next state x[k+1]
f ts ths_w ths_a (Prst [wv', av', q', a', v', p']) (Prst [(w0', a0'), (w1', a1'), (w2', a2')]) 
  = Prst [wv, av, q, a, v, p]
  where (w0, w1, w2) = (from3tupleQ w0', from3tupleQ w1', from3tupleQ w2')
        (a0, a1, a2) = (from3tupleQ a0', from3tupleQ a1', from3tupleQ a2')
        wv = voter ths_w w0 w1 w2 wv'
        av = voter ths_a a0 a1 a2 av'
        q = q' * expQ(mulQR wv (ts/2))
        a = from3tupleQ (0,0,-9.81) + rotQ q av
        v = mulQR (a + a') (ts/2) + v'
        p = mulQR (v + v') (ts/2) + p'
f _ _ _ _ _ = Abst

g :: Float  -- ^ Sampling period
  -> Float  -- ^ threshold for the voter of w
  -> Float  -- ^ threshold for the voter of a
  -> AbstExt [Quaternion Float] -- ^ Current state x[k] = [wv, av, q, a, v, p]
  -> AbstExt [ImuVal]   -- ^ List with the outputs from the three IMUs as pairs (w, a)
  -> AbstExt ([Quaternion Float], [Vec])  -- ^ Outputs (x[k+1], y[k]) = [eulerAngs, aVec, vVec, pVec, nz]
g ts ths_w ths_a (Prst [wv', av', q', a', v', p']) (Prst [(w0', a0'), (w1', a1'), (w2', a2')]) 
  = Prst ([wv, av, q, a, v, p], [eulerAngs, aVec, vVec, pVec, nz])
  where (w0, w1, w2) = (from3tupleQ w0', from3tupleQ w1', from3tupleQ w2')
        (a0, a1, a2) = (from3tupleQ a0', from3tupleQ a1', from3tupleQ a2')
        wv = voter ths_w w0 w1 w2 wv'
        av = voter ths_a a0 a1 a2 av'
        q = q' * expQ(mulQR wv (ts/2))
        a = from3tupleQ (0,0,-9.81) + rotQ q av
        v = mulQR (a + a') (ts/2) + v'
        p = mulQR (v + v') (ts/2) + p'
        eulerAngs = quat2euler q
        aVec = imagQ a
        vVec = imagQ v
        pVec = imagQ p
        nz = (0, 0, (quat2list av !! 3)/9.81)
g _ _ _ _ _ = Abst


config :: (AbstExt [Quaternion Float] -> AbstExt [ImuVal] -> AbstExt [Quaternion Float],
 AbstExt [Quaternion Float] -> AbstExt [ImuVal] -> AbstExt ([Quaternion Float], [Vec]),
 Integer)
config = (f 0.01 0.1 0.1, g 0.01 0.1 0.1, 10)