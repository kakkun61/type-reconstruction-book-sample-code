module TypeReconstruction where

import           Prelude         hiding (Integer)

import qualified Data.List       as List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set

-- #@@range_begin(term)
data Term
  = ValueVariable VariableName
  | IntegerValue Int
  | BooleanValue Bool
  | Plus Term Term
  | If Term Term Term
  | Abstract VariableName Term
  | Application Term Term
  deriving (Show, Eq)
-- #@@range_end(term)

-- #@@range_begin(type)
data Type
  = TypeVariable VariableName
  | Integer
  | Boolean
  | Arrow Type Type
  deriving (Show, Eq, Ord)
-- #@@range_end(type)

-- #@@range_begin(other_type)
type Context = Map VariableName Type

type Constraint = Set (Type, Type)

type Assign = (VariableName, Type)

type VariableName = String
-- #@@range_end(other_type)

-- | 型から自由型変数を抽出する
freeVariables :: Type -> Set VariableName
freeVariables (TypeVariable x) = Set.singleton x
freeVariables Integer = Set.empty
freeVariables Boolean = Set.empty
freeVariables (Arrow t1 t2) = Set.union (freeVariables t1) (freeVariables t2)

-- #@@range_begin(unify)
-- | 単一化関数
unify :: Constraint -> Either String [Assign]
unify c
  -- 制約が空の場合は代入のリストも空である
  | Set.null c = pure []
  | otherwise =
      let
        -- 制約 c から1つ等式を取り出す
        eq = Set.elemAt 0 c
        -- 残りの制約を c' とする
        c' = Set.deleteAt 0 c
      in
        case eq of
          -- 両辺が同一なら無視する
          (s, t) | s == t -> unify c'
          -- 左辺が型変数でそれが右辺の自由変数でないとき
          (TypeVariable x, t) | Set.notMember x (freeVariables t) -> do
            let a = (x, t)
            -- 制約に代入し再帰的に単一化する
            as <- unify (assignConstraint [a] c')
            -- 効率のため代入のリストは数式と左右反転させている
            pure (a:as)
          -- 右辺が変数のときも同様
          (s, TypeVariable x) | Set.notMember x (freeVariables s) -> do
            let a = (x, s)
            as <- unify (assignConstraint [a] c')
            pure (a:as)
          -- 両辺が関数型のときは分解し制約に加え再帰的に単一化する
          (Arrow s1 s2, Arrow t1 t2) ->
            unify (Set.insert (s1, t1) (Set.insert (s2, t2) c'))
          -- それ以外のときはエラーメッセージを返す
          _ -> Left "invalid constraints"
-- #@@range_end(unify)

-- | 型への代入
assignType :: [Assign] -> Type -> Type
assignType as t =
  List.foldl' (flip assignType') t as

assignType' :: Assign -> Type -> Type
assignType' (y, s) t'@(TypeVariable x)
  | x == y = s
  | otherwise = t'
assignType' _ Integer = Integer
assignType' _ Boolean = Boolean
assignType' a (Arrow t1 t2) = Arrow (assignType' a t1) (assignType' a t2)

-- | 制約への代入
assignConstraint :: [Assign] -> Constraint -> Constraint
assignConstraint as cst =
  List.foldl' go cst as
  where
    go cst' a = Set.map (\(t1, t2) -> (assignType' a t1, assignType' a t2)) cst'

-- #@@range_begin(constraint_type)
-- | 制約型付け
constraintType
  :: Context -- ^ 文脈
  -> Term -- ^ 項
  -> [VariableName] -- ^ 未使用変数名のリスト
  -> Either String (Type, Constraint, [VariableName])
  -- ^ 失敗時は文字列、成功時は型・制約・未使用の変数名のリスト
-- CT-Int
constraintType _ (IntegerValue _) names = pure (Integer, Set.empty, names)
-- CT-True, CT-False
constraintType _ (BooleanValue _) names = pure (Boolean, Set.empty, names)
-- CT-Var
constraintType ctx (ValueVariable x) names = do
  typ <-
    -- 文脈から変数に対応する型を探す
    case Map.lookup x ctx of
      Just typ' -> pure typ'
      -- なければエラーメッセージを返す
      Nothing ->
        Left ("the context (" <> show (Map.toList ctx)
              <> ") doesn't have type variable (" <> x <> ")")
  pure (typ, Set.empty, names)
-- CT-Plus
constraintType ctx (Plus t1 t2) names = do
  -- オペンランドに対して再帰的に適用する
  (typ1, cst1, names1) <- constraintType ctx t1 names
  (typ2, cst2, names2) <- constraintType ctx t2 names1
  let
    -- 制約の和を取る
    cst =
      Set.unions [cst1, cst2, Set.fromList [(typ1, Integer), (typ2, Integer)]]
  pure (Integer, cst, names2)
-- CT-If
constraintType ctx (If t1 t2 t3) names = do
  (typ1, cst1, names1) <- constraintType ctx t1 names
  (typ2, cst2, names2) <- constraintType ctx t2 names1
  (typ3, cst3, names3) <- constraintType ctx t3 names2
  let
    cst =
      Set.unions [cst1, cst2, cst3, Set.fromList [(typ1, Boolean), (typ2, typ3)]]
  pure (typ2, cst, names3)
-- CT-Abs
constraintType ctx (Abstract x t1) names = do
  -- 未使用の変数名から型変数の型を作り、それと残った変数名のリストを得る
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
-- #@@range_end(constraint_type)

newTypeVariable :: [VariableName] -> Either String (Type, [VariableName])
newTypeVariable (n:names) = pure (TypeVariable n, names)
newTypeVariable []        = Left "no unused type variables"
