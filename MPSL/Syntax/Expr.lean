import MPSL.Syntax.Ty

set_option autoImplicit false

namespace MPSL

universe u v

/-- A typed de Bruijn variable in an object-language context. -/
inductive Var : List Ty -> Ty -> Type where
  | here {ty : Ty} {ctx : List Ty} : Var (ty :: ctx) ty
  | there {ctx : List Ty} {ty other : Ty} : Var ctx ty -> Var (other :: ctx) ty

/-- Intrinsically typed syntax for the MPSL term and assertion language. -/
inductive Expr (Loc : Type u) (Val : Type v) : List Ty -> Ty -> Type (max u v) where
  | var {ctx : List Ty} {ty : Ty} : Var ctx ty -> Expr Loc Val ctx ty
  | embed {ctx : List Ty} {ty : Ty} : Expr Loc Val [] ty -> Expr Loc Val ctx ty
  | loc {ctx : List Ty} : Loc -> Expr Loc Val ctx .loc
  | val {ctx : List Ty} : Val -> Expr Loc Val ctx .val
  | unit {ctx : List Ty} : Expr Loc Val ctx .unit
  | lam {ctx : List Ty} {arg result : Ty} :
      Expr Loc Val (arg :: ctx) result -> Expr Loc Val ctx (.arr arg result)
  | app {ctx : List Ty} {arg result : Ty} :
      Expr Loc Val ctx (.arr arg result) -> Expr Loc Val ctx arg -> Expr Loc Val ctx result
  | pair {ctx : List Ty} {left right : Ty} :
      Expr Loc Val ctx left -> Expr Loc Val ctx right -> Expr Loc Val ctx (.prod left right)
  | fst {ctx : List Ty} {left right : Ty} :
      Expr Loc Val ctx (.prod left right) -> Expr Loc Val ctx left
  | snd {ctx : List Ty} {left right : Ty} :
      Expr Loc Val ctx (.prod left right) -> Expr Loc Val ctx right
  | inl {ctx : List Ty} {left : Ty} (right : Ty) :
      Expr Loc Val ctx left -> Expr Loc Val ctx (.sum left right)
  | inr {ctx : List Ty} (left : Ty) {right : Ty} :
      Expr Loc Val ctx right -> Expr Loc Val ctx (.sum left right)
  | case {ctx : List Ty} {left right result : Ty} :
      Expr Loc Val ctx (.sum left right) ->
      Expr Loc Val (left :: ctx) result ->
      Expr Loc Val (right :: ctx) result ->
      Expr Loc Val ctx result
  | falsum {ctx : List Ty} : Expr Loc Val ctx .iprop
  | truth {ctx : List Ty} : Expr Loc Val ctx .iprop
  | eq {ctx : List Ty} {ty : Ty} :
      Expr Loc Val ctx ty -> Expr Loc Val ctx ty -> Expr Loc Val ctx .iprop
  | imp {ctx : List Ty} :
      Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop
  | and {ctx : List Ty} :
      Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop
  | or {ctx : List Ty} :
      Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop
  | sep {ctx : List Ty} :
      Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop
  | wand {ctx : List Ty} :
      Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop
  | ex {ctx : List Ty} {ty : Ty} :
      Expr Loc Val (ty :: ctx) .iprop -> Expr Loc Val ctx .iprop
  | all {ctx : List Ty} {ty : Ty} :
      Expr Loc Val (ty :: ctx) .iprop -> Expr Loc Val ctx .iprop
  | pointsTo {ctx : List Ty} :
      Expr Loc Val ctx .loc -> Expr Loc Val ctx .val -> Expr Loc Val ctx .iprop
  | always {ctx : List Ty} : Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop
  | later {ctx : List Ty} : Expr Loc Val ctx .iprop -> Expr Loc Val ctx .iprop

abbrev Formula (Loc : Type u) (Val : Type v) := Expr Loc Val [] .iprop

end MPSL
