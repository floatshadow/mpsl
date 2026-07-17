import Lean.Elab.Term
import MPSL.Syntax.Expr

set_option autoImplicit false

declare_syntax_cat mpslTy
syntax:max "loc" : mpslTy
syntax:max "val" : mpslTy
syntax:max "iProp" : mpslTy
syntax:max num : mpslTy
syntax:max "𝟘" : mpslTy
syntax:max "𝟙" : mpslTy
syntax:max "(" mpslTy ")" : mpslTy
syntax:70 mpslTy:71 " × " mpslTy:70 : mpslTy
syntax:65 mpslTy:66 " + " mpslTy:65 : mpslTy
syntax:60 mpslTy:61 " -> " mpslTy:60 : mpslTy
syntax:60 mpslTy:61 " → " mpslTy:60 : mpslTy

declare_syntax_cat mpslTerm
syntax:max ident : mpslTerm
syntax:max "loc(" term ")" : mpslTerm
syntax:max "val(" term ")" : mpslTerm
syntax:max "embed[" mpslTy "](" term ")" : mpslTerm
syntax:max "()" : mpslTerm
syntax:max "False" : mpslTerm
syntax:max "True" : mpslTerm
syntax:max "(" mpslTerm ")" : mpslTerm
syntax:max "(" mpslTerm ", " mpslTerm ")" : mpslTerm
syntax:max "fst " mpslTerm:max : mpslTerm
syntax:max "snd " mpslTerm:max : mpslTerm
syntax:max "inl[" mpslTy "](" mpslTerm ")" : mpslTerm
syntax:max "inr[" mpslTy "](" mpslTerm ")" : mpslTerm
syntax:max "eq[" mpslTy "](" mpslTerm ", " mpslTerm ")" : mpslTerm
syntax:90 mpslTerm:90 "(" mpslTerm ")" : mpslTerm
syntax:80 "always " mpslTerm:80 : mpslTerm
syntax:80 "later " mpslTerm:80 : mpslTerm
syntax:70 mpslTerm:71 " |-> " mpslTerm:71 : mpslTerm
syntax:65 mpslTerm:66 " =[" mpslTy "] " mpslTerm:65 : mpslTerm
syntax:60 mpslTerm:61 " * " mpslTerm:60 : mpslTerm
syntax:55 mpslTerm:56 " /\\ " mpslTerm:55 : mpslTerm
syntax:54 mpslTerm:55 " \\/ " mpslTerm:54 : mpslTerm
syntax:50 mpslTerm:51 " -* " mpslTerm:50 : mpslTerm
syntax:45 mpslTerm:46 " -> " mpslTerm:45 : mpslTerm
syntax:40 "fun " ident " : " mpslTy " => " mpslTerm:40 : mpslTerm
syntax:40 "λ " ident " : " mpslTy ", " mpslTerm:40 : mpslTerm
syntax:40 "forall " ident " : " mpslTy ", " mpslTerm:40 : mpslTerm
syntax:40 "exists " ident " : " mpslTy ", " mpslTerm:40 : mpslTerm
syntax:35 "case" mpslTerm "of" "|" "inl" ident "=>" mpslTerm
  "|" "inr" ident "=>" mpslTerm : mpslTerm

syntax:55 mpslTerm:56 " ∧ " mpslTerm:55 : mpslTerm
syntax:54 mpslTerm:55 " ∨ " mpslTerm:54 : mpslTerm
syntax:60 mpslTerm:61 " ∗ " mpslTerm:60 : mpslTerm
syntax:50 mpslTerm:51 " -∗ " mpslTerm:50 : mpslTerm
syntax:45 mpslTerm:46 " ⇒ " mpslTerm:45 : mpslTerm
syntax:70 mpslTerm:71 " ↦ " mpslTerm:71 : mpslTerm
syntax:80 "□ " mpslTerm:80 : mpslTerm
syntax:80 "▷ " mpslTerm:80 : mpslTerm
syntax:40 "∀ " ident " : " mpslTy ", " mpslTerm:40 : mpslTerm
syntax:40 "∃ " ident " : " mpslTy ", " mpslTerm:40 : mpslTerm

syntax:max "mpsl{" mpslTerm "}" : term

namespace MPSL.Elab

open Lean Lean.Elab Lean.Elab.Term

private structure CompiledTy where
  value : Ty
  term : TSyntax `term

private structure CompiledExpr where
  ty : Ty
  term : TSyntax `term

private structure Binding where
  name : Name
  ty : Ty

private abbrev Context := List Binding

private def expectType (ref : Syntax) (actual expected : Ty) : TermElabM Unit :=
  unless actual = expected do
    throwErrorAt ref "MPSL type mismatch: expected {expected.format}, got {actual.format}"

private def expectSameType (ref : Syntax) (left right : Ty) : TermElabM Unit :=
  unless left = right do
    throwErrorAt ref "MPSL type mismatch: left side has type {left.format}, right side has type {right.format}"

private partial def compileTy : Syntax -> TermElabM CompiledTy
  | `(mpslTy| loc) => return ⟨.loc, ← `(MPSL.Ty.loc)⟩
  | `(mpslTy| val) => return ⟨.val, ← `(MPSL.Ty.val)⟩
  | `(mpslTy| iProp) => return ⟨.iprop, ← `(MPSL.Ty.iprop)⟩
  | stx@`(mpslTy| $number:num) =>
      match number.raw.isNatLit? with
      | some 0 => return ⟨.empty, ← `(MPSL.Ty.empty)⟩
      | some 1 => return ⟨.unit, ← `(MPSL.Ty.unit)⟩
      | _ => throwErrorAt stx "MPSL only supports the type constants 0 and 1"
  | `(mpslTy| 𝟘) => return ⟨.empty, ← `(MPSL.Ty.empty)⟩
  | `(mpslTy| 𝟙) => return ⟨.unit, ← `(MPSL.Ty.unit)⟩
  | `(mpslTy| ($ty:mpslTy)) => compileTy ty
  | `(mpslTy| $left:mpslTy × $right:mpslTy) => do
      let left ← compileTy left
      let right ← compileTy right
      return ⟨.prod left.value right.value, ← `(MPSL.Ty.prod $(left.term) $(right.term))⟩
  | `(mpslTy| $left:mpslTy + $right:mpslTy) => do
      let left ← compileTy left
      let right ← compileTy right
      return ⟨.sum left.value right.value, ← `(MPSL.Ty.sum $(left.term) $(right.term))⟩
  | `(mpslTy| $domain:mpslTy -> $codomain:mpslTy) => do
      let domain ← compileTy domain
      let codomain ← compileTy codomain
      return ⟨.arr domain.value codomain.value,
        ← `(MPSL.Ty.arr $(domain.term) $(codomain.term))⟩
  | `(mpslTy| $domain:mpslTy → $codomain:mpslTy) => do
      let domain ← compileTy domain
      let codomain ← compileTy codomain
      return ⟨.arr domain.value codomain.value,
        ← `(MPSL.Ty.arr $(domain.term) $(codomain.term))⟩
  | stx => throwErrorAt stx "unsupported MPSL type syntax"

private def findBinding (ctx : Context) (name : Name) : Option (Nat × Ty) :=
  let rec go (index : Nat) : Context -> Option (Nat × Ty)
    | [] => none
    | binding :: rest =>
        if binding.name = name then some (index, binding.ty) else go (index + 1) rest
  go 0 ctx

private partial def compileVar : Nat -> TermElabM (TSyntax `term)
  | 0 => `(MPSL.Var.here)
  | index + 1 => do
      let rest ← compileVar index
      `(MPSL.Var.there $rest)

private def compileBinaryIProp
    (compile : Syntax -> TermElabM CompiledExpr)
    (ref : Syntax) (left right : Syntax) (ctor : Name) :
    TermElabM CompiledExpr := do
  let left ← compile left
  let right ← compile right
  expectType left.term left.ty .iprop
  expectType right.term right.ty .iprop
  let term ← match ctor with
    | ``MPSL.Expr.imp => `(MPSL.Expr.imp $(left.term) $(right.term))
    | ``MPSL.Expr.and => `(MPSL.Expr.and $(left.term) $(right.term))
    | ``MPSL.Expr.or => `(MPSL.Expr.or $(left.term) $(right.term))
    | ``MPSL.Expr.sep => `(MPSL.Expr.sep $(left.term) $(right.term))
    | ``MPSL.Expr.wand => `(MPSL.Expr.wand $(left.term) $(right.term))
    | _ => throwErrorAt ref "internal MPSL elaborator error: unknown connective"
  return ⟨.iprop, term⟩

private partial def compileExpr (ctx : Context) : Syntax -> TermElabM CompiledExpr
  | stx@`(mpslTerm| $name:ident) => do
      let some (index, ty) := findBinding ctx name.getId
        | throwErrorAt stx "unknown MPSL variable '{name.getId}'"
      let var ← compileVar index
      return ⟨ty, ← `(MPSL.Expr.var $var)⟩
  | `(mpslTerm| loc($value:term)) =>
      return ⟨.loc, ← `(MPSL.Expr.loc $value)⟩
  | `(mpslTerm| val($value:term)) =>
      return ⟨.val, ← `(MPSL.Expr.val $value)⟩
  | `(mpslTerm| embed[$ty:mpslTy]($value:term)) => do
      let ty ← compileTy ty
      return ⟨ty.value, ← `(MPSL.Expr.embed (ty := $(ty.term)) $value)⟩
  | `(mpslTerm| ()) => return ⟨.unit, ← `(MPSL.Expr.unit)⟩
  | `(mpslTerm| False) => return ⟨.iprop, ← `(MPSL.Expr.falsum)⟩
  | `(mpslTerm| True) => return ⟨.iprop, ← `(MPSL.Expr.truth)⟩
  | `(mpslTerm| ($body:mpslTerm)) => compileExpr ctx body
  | `(mpslTerm| ($left:mpslTerm, $right:mpslTerm)) => do
      let left ← compileExpr ctx left
      let right ← compileExpr ctx right
      return ⟨.prod left.ty right.ty, ← `(MPSL.Expr.pair $(left.term) $(right.term))⟩
  | stx@`(mpslTerm| fst $pair:mpslTerm) => do
      let pair ← compileExpr ctx pair
      match pair.ty with
      | .prod left _ => return ⟨left, ← `(MPSL.Expr.fst $(pair.term))⟩
      | actual => throwErrorAt stx "MPSL 'fst' expects a product, got {actual.format}"
  | stx@`(mpslTerm| snd $pair:mpslTerm) => do
      let pair ← compileExpr ctx pair
      match pair.ty with
      | .prod _ right => return ⟨right, ← `(MPSL.Expr.snd $(pair.term))⟩
      | actual => throwErrorAt stx "MPSL 'snd' expects a product, got {actual.format}"
  | `(mpslTerm| inl[$rightTy:mpslTy]($value:mpslTerm)) => do
      let rightTy ← compileTy rightTy
      let value ← compileExpr ctx value
      return ⟨.sum value.ty rightTy.value,
        ← `(MPSL.Expr.inl $(rightTy.term) $(value.term))⟩
  | `(mpslTerm| inr[$leftTy:mpslTy]($value:mpslTerm)) => do
      let leftTy ← compileTy leftTy
      let value ← compileExpr ctx value
      return ⟨.sum leftTy.value value.ty,
        ← `(MPSL.Expr.inr $(leftTy.term) $(value.term))⟩
  | stx@`(mpslTerm| $function:mpslTerm($argument:mpslTerm)) => do
      let function ← compileExpr ctx function
      let argument ← compileExpr ctx argument
      match function.ty with
      | .arr domain codomain =>
          expectType stx argument.ty domain
          return ⟨codomain, ← `(MPSL.Expr.app $(function.term) $(argument.term))⟩
      | actual => throwErrorAt stx "MPSL application expects a function, got {actual.format}"
  | `(mpslTerm| fun $name:ident : $argTy:mpslTy => $body:mpslTerm) => do
      let argTy ← compileTy argTy
      let body ← compileExpr (⟨name.getId, argTy.value⟩ :: ctx) body
      return ⟨.arr argTy.value body.ty,
        ← `(MPSL.Expr.lam (arg := $(argTy.term)) $(body.term))⟩
  | `(mpslTerm| λ $name:ident : $argTy:mpslTy, $body:mpslTerm) => do
      let argTy ← compileTy argTy
      let body ← compileExpr (⟨name.getId, argTy.value⟩ :: ctx) body
      return ⟨.arr argTy.value body.ty,
        ← `(MPSL.Expr.lam (arg := $(argTy.term)) $(body.term))⟩
  | stx@`(mpslTerm| case $scrutinee:mpslTerm of
      | inl $leftName:ident => $leftBody:mpslTerm
      | inr $rightName:ident => $rightBody:mpslTerm) => do
      let scrutinee ← compileExpr ctx scrutinee
      match scrutinee.ty with
      | .sum leftTy rightTy =>
          let leftBody ← compileExpr (⟨leftName.getId, leftTy⟩ :: ctx) leftBody
          let rightBody ← compileExpr (⟨rightName.getId, rightTy⟩ :: ctx) rightBody
          expectSameType stx leftBody.ty rightBody.ty
          return ⟨leftBody.ty,
            ← `(MPSL.Expr.case $(scrutinee.term) $(leftBody.term) $(rightBody.term))⟩
      | actual => throwErrorAt stx "MPSL 'case' expects a sum, got {actual.format}"
  | stx@`(mpslTerm| eq[$ty:mpslTy]($left:mpslTerm, $right:mpslTerm)) => do
      let ty ← compileTy ty
      let left ← compileExpr ctx left
      let right ← compileExpr ctx right
      expectType stx left.ty ty.value
      expectType stx right.ty ty.value
      return ⟨.iprop,
        ← `(MPSL.Expr.eq (ty := $(ty.term)) $(left.term) $(right.term))⟩
  | stx@`(mpslTerm| $left:mpslTerm =[$ty:mpslTy] $right:mpslTerm) => do
      let ty ← compileTy ty
      let left ← compileExpr ctx left
      let right ← compileExpr ctx right
      expectType stx left.ty ty.value
      expectType stx right.ty ty.value
      return ⟨.iprop,
        ← `(MPSL.Expr.eq (ty := $(ty.term)) $(left.term) $(right.term))⟩
  | stx@`(mpslTerm| $location:mpslTerm |-> $value:mpslTerm) => do
      let location ← compileExpr ctx location
      let value ← compileExpr ctx value
      expectType stx location.ty .loc
      expectType stx value.ty .val
      return ⟨.iprop, ← `(MPSL.Expr.pointsTo $(location.term) $(value.term))⟩
  | stx@`(mpslTerm| $location:mpslTerm ↦ $value:mpslTerm) => do
      let location ← compileExpr ctx location
      let value ← compileExpr ctx value
      expectType stx location.ty .loc
      expectType stx value.ty .val
      return ⟨.iprop, ← `(MPSL.Expr.pointsTo $(location.term) $(value.term))⟩
  | stx@`(mpslTerm| $left:mpslTerm * $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.sep
  | stx@`(mpslTerm| $left:mpslTerm ∗ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.sep
  | stx@`(mpslTerm| $left:mpslTerm /\ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.and
  | stx@`(mpslTerm| $left:mpslTerm ∧ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.and
  | stx@`(mpslTerm| $left:mpslTerm \/ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.or
  | stx@`(mpslTerm| $left:mpslTerm ∨ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.or
  | stx@`(mpslTerm| $left:mpslTerm -* $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.wand
  | stx@`(mpslTerm| $left:mpslTerm -∗ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.wand
  | stx@`(mpslTerm| $left:mpslTerm -> $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.imp
  | stx@`(mpslTerm| $left:mpslTerm ⇒ $right:mpslTerm) =>
      compileBinaryIProp (compileExpr ctx) stx left right ``MPSL.Expr.imp
  | stx@`(mpslTerm| always $body:mpslTerm) => do
      let body ← compileExpr ctx body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.always $(body.term))⟩
  | stx@`(mpslTerm| □ $body:mpslTerm) => do
      let body ← compileExpr ctx body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.always $(body.term))⟩
  | stx@`(mpslTerm| later $body:mpslTerm) => do
      let body ← compileExpr ctx body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.later $(body.term))⟩
  | stx@`(mpslTerm| ▷ $body:mpslTerm) => do
      let body ← compileExpr ctx body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.later $(body.term))⟩
  | stx@`(mpslTerm| forall $name:ident : $ty:mpslTy, $body:mpslTerm) => do
      let ty ← compileTy ty
      let body ← compileExpr (⟨name.getId, ty.value⟩ :: ctx) body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.all (ty := $(ty.term)) $(body.term))⟩
  | stx@`(mpslTerm| ∀ $name:ident : $ty:mpslTy, $body:mpslTerm) => do
      let ty ← compileTy ty
      let body ← compileExpr (⟨name.getId, ty.value⟩ :: ctx) body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.all (ty := $(ty.term)) $(body.term))⟩
  | stx@`(mpslTerm| exists $name:ident : $ty:mpslTy, $body:mpslTerm) => do
      let ty ← compileTy ty
      let body ← compileExpr (⟨name.getId, ty.value⟩ :: ctx) body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.ex (ty := $(ty.term)) $(body.term))⟩
  | stx@`(mpslTerm| ∃ $name:ident : $ty:mpslTy, $body:mpslTerm) => do
      let ty ← compileTy ty
      let body ← compileExpr (⟨name.getId, ty.value⟩ :: ctx) body
      expectType stx body.ty .iprop
      return ⟨.iprop, ← `(MPSL.Expr.ex (ty := $(ty.term)) $(body.term))⟩
  | stx => throwErrorAt stx "unsupported MPSL expression syntax"

elab_rules : term <= expectedType
  | `(mpsl{ $body:mpslTerm }) => do
      let body ← compileExpr [] body
      expectType body.term body.ty .iprop
      elabTerm body.term (some expectedType)

end MPSL.Elab
