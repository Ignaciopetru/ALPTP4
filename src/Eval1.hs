module Eval1
  ( eval
  , Env
  )
where

import           AST
import           Monads
import qualified Data.Map.Strict               as M
import           Data.Maybe
import           Prelude                 hiding ( fst
                                                , snd
                                                )
import           Data.Strict.Tuple
import           Control.Monad                  ( liftM
                                                , ap
                                                )

-- Entornos
type Env = M.Map Variable Int

-- Entorno nulo
initEnv :: Env
initEnv = M.empty

-- Mónada estado
newtype State a = State { runState :: Env -> Pair a Env }

instance Monad State where
  return x = State (\s -> (x :!: s))
  m >>= f = State (\s -> let (v :!: s') = runState m s in runState (f v) s')

-- Para calmar al GHC
instance Functor State where
  fmap = liftM

instance Applicative State where
  pure  = return
  (<*>) = ap

instance MonadState State where
  lookfor v = State (\s -> (lookfor' v s :!: s))
    where lookfor' v s = fromJust $ M.lookup v s
  update v i = State (\s -> (() :!: update' v i s)) where update' = M.insert

-- Ejercicio 1.b: Implementar el evaluador utilizando la monada State

-- Evalua un programa en el estado nulo
eval :: Comm -> Env
eval p = snd (runState (stepCommStar p) initEnv)

-- Evalua multiples pasos de un comando, hasta alcanzar un Skip
stepCommStar :: MonadState m => Comm -> m ()
stepCommStar Skip = return ()
stepCommStar c    = stepComm c >>= \c' -> stepCommStar c'

-- Evalua un paso de un comando
stepComm :: MonadState m => Comm -> m Comm
stepComm Skip = return Skip
stepComm (Let var exp) = do val <- evalExp exp
                            update var val
                            return Skip
stepComm (Seq comm1 comm2) = case comm1 of
                                  Skip -> stepComm comm2
                                  _ -> do evalComm1 <- stepComm comm1
                                          stepComm (Seq evalComm1 comm2)
stepComm (IfThenElse cond true false) = do condV <- evalExp cond
                                           if condV then stepComm true
                                                    else stepComm false
stepComm (While cond comm) = do condV <- evalExp cond
                                if condV then stepComm (Seq comm (While cond comm))
                                          else stepComm Skip


doubleEvalAndApply :: MonadState m => (a -> a -> b) -> Exp a -> Exp a -> m b
doubleEvalAndApply f exp1 exp2 = do exp1V <- evalExp exp1
                                    exp2V <- evalExp exp2
                                    return (f exp1V exp2V)

-- Evalua una expresion
evalExp :: MonadState m => Exp a -> m a
evalExp (Const c) = return c
evalExp (Var v) = lookfor v
evalExp (UMinus n) = do nV <- evalExp n
                        return (-nV)
evalExp (Plus n1 n2) = doubleEvalAndApply (\x y -> x + y) n1 n2
evalExp (Minus n1 n2) = doubleEvalAndApply (\x y -> x - y) n1 n2
evalExp (Times n1 n2) = doubleEvalAndApply (\x y -> x * y) n1 n2
evalExp (Div n1 n2) = doubleEvalAndApply (\x y -> div x y) n1 n2
evalExp BTrue = return True
evalExp BFalse = return False
evalExp (Lt n1 n2) = doubleEvalAndApply (\x y -> x < y) n1 n2
evalExp (Gt n1 n2) = doubleEvalAndApply (\x y -> x > y) n1 n2
evalExp (And n1 n2) = doubleEvalAndApply (\x y -> x && y) n1 n2
evalExp (Or n1 n2) = doubleEvalAndApply (\x y -> x || y) n1 n2 
evalExp (Not e) = do eV <- evalExp e
                     return (not eV)
evalExp (Eq n1 n2) = doubleEvalAndApply (\x y -> x == y) n1 n2 
evalExp (NEq n1 n2) = doubleEvalAndApply (\x y -> x /= y) n1 n2
evalExp (EAssgn s e) = do v <- evalExp e
                          update s v
                          return v
evalExp (ESeq n1 n2) = do evalExp n1
                          evalExp n2


