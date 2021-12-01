module Eval3
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

-- Ejercicio 3.a: Proponer una nueva m\'onada que  
-- lleve una traza de ejecución (además de manejar errores y estado).
-- y dar su instancia de mónada. Llamarla |StateErrorTrace|. 
newtype StateErrorTrace a = StateErrorTrace { runStateErrorTrace :: Env -> Either Error (Pair a Env,Trace) }

-- Recuerde agregar las siguientes instancias para calmar al GHC:
instance Functor StateErrorTrace where
  fmap = liftM

instance Applicative StateErrorTrace where
  pure  = return
  (<*>) = ap

instance Monad StateErrorTrace where
  return x = StateErrorTrace (\s -> Right ((x :!: s),""))
  m >>= f = StateErrorTrace (\s -> do ((v :!: s'),n) <- runStateErrorTrace m s
                                      ((u :!: t ),n') <- runStateErrorTrace (f v) s'
                                      return ((u :!: t), n ++ n'))

-- Ejercicio 3.c: Dar una instancia de MonadTrace para StateErrorTrace.
instance MonadTrace StateErrorTrace where
  trace t = StateErrorTrace (\s -> Right ((() :!: s),t))


-- Ejercicio 3.d: Dar una instancia de MonadError para StateErrorTrace.
instance MonadError StateErrorTrace where
  throw e = StateErrorTrace (\s -> Left e)

-- Ejercicio 3.e: Dar una instancia de MonadState para StateErrorTrace.
instance MonadState StateErrorTrace where
  lookfor v = StateErrorTrace (\s -> case M.lookup v s of
                                      Nothing -> Left UndefVar
                                      Just x -> Right ((x :!: s),""))

  update v i = StateErrorTrace (\s -> Right ((() :!:update' v i s),"")) where update' = M.insert 

-- Ejercicio 3.f: Implementar el evaluador utilizando la monada StateErrorTrace.
-- Evalua un programa en el estado nulo
eval :: Comm -> Either Error (Env, Trace)
eval p = runStateErrorTrace (stepCommStar p) initEnv >>= \((_:!:s),i) -> return (s,i)

-- Evalua multiples pasos de un comando, hasta alcanzar un Skip
stepCommStar :: (MonadState m, MonadError m, MonadTrace m) => Comm -> m ()
stepCommStar Skip = return ()
stepCommStar c    = stepComm c >>= \c' -> stepCommStar c'

-- Evalua un paso de un comando
stepComm ::(MonadState m, MonadError m, MonadTrace m) => Comm -> m Comm
stepComm Skip = return Skip
stepComm (Let var exp) = do val <- evalExp exp
                            update var val
                            trace ("[" ++ var ++ " = " ++ (show val) ++ "] ")
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

doubleEvalAndApply :: (MonadState m, MonadError m, MonadTrace m) => (a -> a -> b) -> Exp a -> Exp a -> m b
doubleEvalAndApply f exp1 exp2 = do exp1V <- evalExp exp1
                                    exp2V <- evalExp exp2
                                    return (f exp1V exp2V)

-- Evalua una expresion 
evalExp :: (MonadState m, MonadError m, MonadTrace m) => Exp a -> m a
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