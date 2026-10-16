/-
On v4.35.0 the kernel accepts every declaration below with checking on, including
`Exploit.exploit : False`, and the file prints "kernel accepted Exploit.exploit : False".
Once fixed, the kernel should refuse `Exploit.P` large elimination, so `Exploit.f` is rejected.

The constructor's parameter domain is `autoParam Prop Type`, with a dishonest root-level
`autoParam` that unfolds to its second argument. The kernel strips the annotation by name to
`Prop` in `elim_only_at_universe_zero`, so the field `x : p` looks like a proof and `P` gets
large elimination, while `check_constructors` sees the domain unfold to `Type`. Init declares the
honest `autoParam`, so the environment is built from `Init.Prelude` with `addDeclCore`.
Adapted from https://github.com/gersh/lean-kernel-bug.
-/

import Lean
open Lean

def check (env : Environment) (d : Declaration) : IO Environment := do
  match env.addDeclCore 1000000 10000 d (cancelTk? := none) (doCheck := true) with
  | .ok env => pure env
  | .error e => throw (IO.userError s!"kernel rejected: {← (e.toMessageData {}).toString}")

#eval show IO Unit from do
  let prop := Expr.sort 0
  let type := Expr.sort 1
  let type1 := Expr.sort 2
  let bool := Expr.const ``Bool []
  let mut env ← importModules #[{ module := `Init.Prelude }] {} 0
  -- `autoParam (A : Type) (B : Type 1) : Type 1 := B`
  env ← check env <| .defnDecl
    { name := `autoParam, levelParams := [], type := .forallE `A type (.forallE `B type1 type1 .default) .default
      value := .lam `A type (.lam `B type1 (.bvar 0) .default) .default, hints := .regular 1, safety := .safe }
  -- `inductive Exploit.P (p : Type) : Prop | mk : (p : autoParam Prop Type) → p → Exploit.P p`
  let mkTy := Expr.forallE `p (mkApp2 (.const `autoParam []) prop type)
    (.forallE `x (.bvar 0) (mkApp (.const `Exploit.P []) (.bvar 1)) .default) .default
  env ← check env <| .inductDecl [] 1
    [{ name := `Exploit.P, type := .forallE `p type prop .default, ctors := [{ name := `Exploit.P.mk, type := mkTy }] }] false
  -- `Exploit.f : Exploit.P Bool → Bool`, recovering the payload of a proof
  let pBool := mkApp (.const `Exploit.P []) bool
  env ← check env <| .defnDecl
    { name := `Exploit.f, levelParams := [], type := .forallE `t pBool bool .default
      value := mkApp3 (.const `Exploit.P.rec [1]) bool (.lam `t pBool bool .default) (.lam `x bool (.bvar 0) .default)
      hints := .regular 1, safety := .safe }
  -- `Exploit.g : Bool → Prop`, with `g false = False` and `g true = True`
  env ← check env <| .defnDecl
    { name := `Exploit.g, levelParams := [], type := .forallE `b bool prop .default
      value := .lam `b bool (mkApp4 (.const ``Bool.rec [1]) (.lam `b bool prop .default)
        (.const ``False []) (.const ``True []) (.bvar 0)) .default
      hints := .regular 1, safety := .safe }
  -- `f (mk Bool true) ≡ f (mk Bool false)` by proof irrelevance; transport `True.intro` to `False`
  let x := mkApp (.const `Exploit.f []) (mkApp2 (.const `Exploit.P.mk []) bool (.const ``Bool.true []))
  let y := mkApp (.const `Exploit.f []) (mkApp2 (.const `Exploit.P.mk []) bool (.const ``Bool.false []))
  let motive := Expr.lam `b bool (.lam `h (mkApp3 (.const ``Eq [1]) bool x (.bvar 0))
    (mkApp (.const `Exploit.g []) (.bvar 1)) .default) .default
  env ← check env <| .thmDecl
    { name := `Exploit.exploit, levelParams := [], type := .const ``False []
      value := mkAppN (.const ``Eq.rec [0, 1]) #[bool, x, motive, .const ``True.intro [], y,
        mkApp2 (.const ``Eq.refl [1]) bool x] }
  IO.println s!"kernel accepted Exploit.exploit : {(env.find? `Exploit.exploit).get!.type}"
