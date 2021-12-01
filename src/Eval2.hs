module Eval2
  ( eval
  , Env
  )
where

import           AST
import           Monads
import qualified Data.Map.Strict               as M
import           Data.Maybe
import           Data.Strict.Tuple
import           Control.Monad                  ( liftM
                                                , ap
                                                )

-- Entornos
type Env = M.Map Variable Int

-- Entorno nulo
initEnv :: Env
initEnv = M.empty

-- Mónada estado, con manejo de errores
newtype StateError a =
  StateError { runStateError :: Env -> Either Error ( Pair a Env) }


-- Para calmar al GHC
instance Functor StateError where
  fmap = liftM

instance Applicative StateError where
  pure  = return
  (<*>) = ap

-- Ejercicio 2.a: Dar una instancia de Monad para StateError:
instance Monad StateError where
  return x = StateError (\s -> Right (x :!: s))
  m >>= f =  StateError (\s -> runStateError m s >>= \(v :!: s') -> runStateError (f v) s')

-- Ejercicio 2.b: Dar una instancia de MonadError para StateError:
instance MonadError StateError where
  throw e = StateError (\s -> Left e)

-- Ejercicio 2.c: Dar una instancia de MonadState para StateError:
instance MonadState StateError where
  lookfor v = StateError (\s -> case M.lookup v s of 
                            Nothing -> Left UndefVar
                            Just x -> Right (x :!: s))
  update v i = StateError (\s -> Right (() :!: update' v i s)) where update' = M.insert
-- Ejercicio 2.d: Implementar el evaluador utilizando la monada StateError.
-- Evalua un programa en el estado nulo
eval :: Comm -> Either Error Env
eval p = runStateError (stepCommStar p) initEnv >>= \(_:!:s) -> return s

-- Evalua multiples pasos de un comando, hasta alcanzar un Skip
stepCommStar :: (MonadState m, MonadError m) => Comm -> m ()
stepCommStar Skip = return ()
stepCommStar c    = stepComm c >>= \c' -> stepCommStar c'

-- Evalua un paso de un comando
stepComm :: (MonadState m, MonadError m) => Comm -> m Comm
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


doubleEvalAndApply :: (MonadState m, MonadError m) => (a -> a -> b) -> Exp a -> Exp a -> m b
doubleEvalAndApply f exp1 exp2 = do exp1V <- evalExp exp1
                                    exp2V <- evalExp exp2
                                    return (f exp1V exp2V)


-- Evalua una expresion
evalExp :: (MonadState m, MonadError m) => Exp a -> m a
evalExp (Const c) = return c
evalExp (Var v) = lookfor v
evalExp (UMinus n) = do nV <- evalExp n
                        return (-nV)
evalExp (Plus n1 n2) = doubleEvalAndApply (\x y -> x + y) n1 n2
evalExp (Minus n1 n2) = doubleEvalAndApply (\x y -> x - y) n1 n2
evalExp (Times n1 n2) = doubleEvalAndApply (\x y -> x * y) n1 n2
evalExp (Div n1 n2) = do n1V <- evalExp n1
                         n2V <- evalExp n2
                         if n2V == 0 then throw DivByZero
                                     else return (div n1V n2V)
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
