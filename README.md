# 『俺々言語にだって型推論が欲しい！』サンプルコード

## 実行方法

### stack のインストール

公式ガイドの手順に従う。

https://docs.haskellstack.org/en/stable/README/#how-to-install

### 対話環境の実行

リポジトリーのルートディレクトリーにて実行する。

```
$ stack repl
```

### 実行例

```
> context = mempty
> term = Abstract "f" (Abstract "x" (If (Application (ValueVariable "f") (ValueVariable "x")) (Application (ValueVariable "f") (IntegerValue 1)) (Application (ValueVariable "f") (IntegerValue 2))))> names = show <$> [1 :: Int ..]
> Right (typ, constraint, names') = constraintType context term names
> typ
Arrow (TypeVariable "1") (Arrow (TypeVariable "2") (TypeVariable "4"))
> constraint
fromList [(TypeVariable "1",Arrow (TypeVariable "2") (TypeVariable "3")),(TypeVariable "1",Arrow Integer (TypeVariable "4")),(TypeVariable "1",Arrow Integer (TypeVariable "5")),(TypeVariable "3",Boolean),(TypeVariable "4",TypeVariable "5")]
> head names'
"6"
> Right assign = unify constraint
> assign
[("1",Arrow (TypeVariable "2") (TypeVariable "3")),("3",Boolean),("4",TypeVariable "5"),("2",Integer),("5",Boolean)]
> assignType assign typ
Arrow (Arrow Integer Boolean) (Arrow Integer Boolean)
> assignConstraint assign constraint
fromList [(Boolean,Boolean),(Arrow Integer Boolean,Arrow Integer Boolean)]
```
