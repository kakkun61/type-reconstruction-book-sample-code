module TypeReconstruction where

import Prelude hiding (Integer, Bool)
import qualified Prelude as P
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List

data Term
  = ValueVariable VariableName
  | IntegerValue P.Int
  | BoolValue P.Bool
  | Plus Term Term
  | If Term Term Term
  | Abstract VariableName Term
  | Application Term Term
  deriving (Show, Eq)

data Type
  = TypeVariable VariableName
  | Integer
  | Bool
  | Arrow Type Type
  deriving (Show, Eq, Ord)

type Context = Map VariableName Type

type Constraint = Set (Type, Type)

type Assign = (VariableName, Type)

type VariableName = String

-- | 型から自由型変数を抽出する
freeVarialbes :: Type -> Set VariableName
freeVarialbes (TypeVariable x) = Set.singleton x
freeVarialbes Integer = Set.empty
freeVarialbes Bool = Set.empty
freeVarialbes (Arrow t1 t2) = Set.union (freeVarialbes t1) (freeVarialbes t2)

-- | 単一化関数
unify :: Constraint -> Either String [Assign]
unify c
  | Set.null c = pure []
  | otherwise =
      let
        eq = Set.elemAt 0 c
        c' = Set.deleteAt 0 c
      in
        case eq of
          (s, t) | s == t -> unify c'
          (TypeVariable x, t) | Set.notMember x (freeVarialbes t) -> do
            let a = (x, t)
            as <- unify (assignConstraint [a] c')
            pure (a:as)
          (s, TypeVariable x) | Set.notMember x (freeVarialbes s) -> do
            let a = (x, s)
            as <- unify (assignConstraint [a] c')
            pure (a:as)
          (Arrow s1 s2, Arrow t1 t2) ->
            unify (Set.insert (s1, t1) (Set.insert (s2, t2) c'))
          _ -> Left "invalid constraints"

-- | 型への代入
assignType :: [Assign] -> Type -> Type
assignType as t =
  List.foldl' (flip assignType') t as

assignType' :: Assign -> Type -> Type
assignType' (y, s) t'@(TypeVariable x)
  | x == y = s
  | otherwise = t'
assignType' _ Integer = Integer
assignType' _ Bool = Bool
assignType' a (Arrow t1 t2) = Arrow (assignType' a t1) (assignType' a t2)

-- | 制約への代入
assignConstraint :: [Assign] -> Constraint -> Constraint
assignConstraint as cst =
  List.foldl' go cst as
  where
    go cst' a = Set.map (\(t1, t2) -> (assignType' a t1, assignType' a t2)) cst'

-- | 制約型付け
constraintType :: Context -> Term -> [VariableName] -> Either String (Type, Constraint, [VariableName])
-- CT-Int
constraintType _ (IntegerValue _) names = pure (Integer, Set.empty, names)
-- CT-True, CT-False
constraintType _ (BoolValue _) names = pure (Bool, Set.empty, names)
-- CT-Var
constraintType ctx (ValueVariable x) names = do
  typ <-
    case Map.lookup x ctx of
      Just typ' -> pure typ'
      Nothing -> Left ("the context (" <> show (Map.toList ctx) <> ") doesn't have type variable (" <> x <> ")")
  pure (typ, Set.empty, names)
-- CT-Plus
constraintType ctx (Plus t1 t2) names = do
  (typ1, cst1, names1) <- constraintType ctx t1 names
  (typ2, cst2, names2) <- constraintType ctx t2 names1
  let cst = Set.unions [cst1, cst2, Set.fromList [(typ1, Integer), (typ2, Integer)]]
  pure (Integer, cst, names2)
-- CT-If
constraintType ctx (If t1 t2 t3) names = do
  (typ1, cst1, names1) <- constraintType ctx t1 names
  (typ2, cst2, names2) <- constraintType ctx t2 names1
  (typ3, cst3, names3) <- constraintType ctx t3 names2
  let cst = Set.unions [cst1, cst2, cst3, Set.fromList [(typ1, Bool), (typ2, typ3)]]
  pure (typ2, cst, names3)
-- CT-Abs
constraintType ctx (Abstract x t1) names = do
  (xt, names0) <- newTypeVariable names
  let ctx0 = Map.insert x xt ctx
  (typ1, cst1, names1) <- constraintType ctx0 t1 names0
  pure (Arrow xt typ1, cst1, names1)
-- CT-App
constraintType ctx (Application t1 t2) names = do
  (typ1, cst1, names1) <- constraintType ctx t1 names
  (typ2, cst2, names2) <- constraintType ctx t2 names1
  (typ, names3) <- newTypeVariable names2
  let cst = Set.unions [cst1, cst2, Set.singleton (typ1, Arrow typ2 typ)]
  pure (typ, cst, names3)

newTypeVariable :: [VariableName] -> Either String (Type, [VariableName])
newTypeVariable (n:names) = pure (TypeVariable n, names)
newTypeVariable [] = Left "no unused type variables"
