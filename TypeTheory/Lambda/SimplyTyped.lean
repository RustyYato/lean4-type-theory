import TypeTheory.Lambda.Defs

namespace LambdaCalc.SimplyTyped

inductive LamType where
| void
| func (arg: LamType) (ret: LamType)

inductive IsWellTyped : List LamType -> Term -> LamType -> Prop where
| var (ctx: List LamType) (index: Nat) (h: index < ctx.length) (ty: LamType) (hty: ty = ctx[index]) :
  IsWellTyped ctx (.var index) ty
| lam (ctx: List LamType) (body: Term) (arg_ty ret_ty: LamType) :
  IsWellTyped (arg_ty::ctx) body ret_ty ->
  IsWellTyped ctx (.lam body) (.func arg_ty ret_ty)
| app (ctx: List LamType) (func arg: Term) (arg_ty ret_ty: LamType) :
  IsWellTyped ctx func (.func arg_ty ret_ty) ->
  IsWellTyped ctx arg arg_ty ->
  IsWellTyped ctx (.app func arg) ret_ty

namespace IsWellTyped

def weaken_at (ctx: List LamType) (ctx_ty ty: LamType) (pos: Nat)
  (hpos: pos <= ctx.length) (term: Term) :
  IsWellTyped ctx term ty ->
  IsWellTyped (ctx.insertIdx pos ctx_ty) (term.weaken pos) ty := by
  intro h
  induction h generalizing pos with
  | var ctx index h ty hty =>
    apply IsWellTyped.var
    · rw [hty]
      split
      rw [List.getElem_insertIdx_of_lt]
      assumption
      rw [List.getElem_insertIdx_of_gt]
      rfl
      omega
    · rw [List.length_insertIdx_of_le_length hpos]
      split <;> omega
  | lam ctx  body arg_ty ret_ty _ ih =>
    apply IsWellTyped.lam
    apply ih (pos + 1)
    apply Nat.succ_le_succ
    assumption
  | app _ _ _ _ _ _ _ ih₀ ih₁ =>
    apply IsWellTyped.app
    apply ih₀
    assumption
    apply ih₁
    assumption

def weaken (ctx: List LamType) (ctx_ty ty: LamType) (term: Term) :
  IsWellTyped ctx term ty ->
  IsWellTyped (ctx_ty::ctx) term.weaken ty := by
  refine weaken_at ctx ctx_ty ty 0 ?_ term
  apply Nat.zero_le

def subst_at
  (ctx: List LamType) (ty: LamType) (pos: Nat)
  (hpos: pos < ctx.length) (repl term: Term) :
  IsWellTyped ctx term ty ->
  IsWellTyped (ctx.eraseIdx pos) repl ctx[pos] ->
  IsWellTyped (ctx.eraseIdx pos) (Term.subst pos repl term) ty := by
  intro h hrepl
  induction h generalizing pos repl with
  | var ctx index h ty hty =>
    unfold Term.subst
    split
    . subst pos
      subst ty
      assumption
    apply IsWellTyped.var
    · rw [hty]
      split
      rw [List.getElem_eraseIdx_of_lt]
      assumption
      rw [List.getElem_eraseIdx_of_ge]
      have : pos < index := by omega
      · congr; omega
      · omega
    · rw [List.length_eraseIdx_of_lt hpos]
      split <;> omega
  | lam ctx  body arg_ty ret_ty _ ih =>
    apply IsWellTyped.lam
    apply ih (pos + 1)
    apply weaken
    assumption
    apply Nat.succ_le_succ
    assumption
  | app _ _ _ _ _ _ _ ih₀ ih₁ =>
    apply IsWellTyped.app
    apply ih₀
    assumption
    apply ih₁
    assumption

def subst (ctx: List LamType) (arg_ty ty: LamType) (repl term: Term) :
  IsWellTyped (arg_ty::ctx) term ty ->
  IsWellTyped ctx repl arg_ty ->
  IsWellTyped ctx (Term.subst 0 repl term) ty := by
  apply subst_at (pos := 0)
  apply Nat.zero_lt_succ

def closed (ctx : List LamType) (term: Term) (ty: LamType) :
  IsWellTyped ctx term ty ->
  term.IsClosedAt ctx.length := by
  intro h
  induction h with
  | var =>
    apply Term.IsClosedAt.var
    assumption
  | lam =>
    apply Term.IsClosedAt.lam
    assumption
  | app =>
    apply Term.IsClosedAt.app
    assumption
    assumption

def weakenN (ctx ctx': List LamType) (ty: LamType) (term: Term) :
  IsWellTyped ctx term ty ->
  IsWellTyped (ctx' ++ ctx) (term.weakenN ctx'.length) ty := by
  induction ctx' with
  | nil => exact id
  | cons ty' ctx' ih =>
    intro h
    apply weaken
    apply ih
    assumption

def subst_closed_term
  (ctx: List LamType)
  (arg_ty ty: LamType) (repl term: Term) :
  IsWellTyped (arg_ty::ctx) term ty ->
  IsWellTyped [] repl arg_ty ->
  IsWellTyped ctx (Term.subst 0 repl term) ty := by
  intro wt repl_wt
  rw [←Term.weakenN_closed _ ctx.length repl_wt.closed]
  apply subst
  assumption
  rw (occs := [1]) [←List.append_nil ctx]
  apply IsWellTyped.weakenN (ctx := [])
  assumption

def det_reduction  (red: DetReductionStep a b) (h: IsWellTyped ctx a ty) :
  IsWellTyped ctx b ty := by
  induction red generalizing ty with
  | subst _ _ _ _ hsubst =>
    subst hsubst
    cases h with
    | app _ _ _ _ _ body_wt arg_wt =>
    cases body_wt with
    | lam _ _ _ _ body_wt =>
    apply subst
    assumption
    assumption
  | app_arg _ _ _ _ _ ih =>
    cases h
    apply IsWellTyped.app
    assumption
    apply ih
    assumption
  | app_func _ _ _ _ ih =>
    cases h
    apply IsWellTyped.app
    apply ih
    assumption
    assumption

def preservation  (red: DetReduction a b) (h: IsWellTyped ctx a ty) :
  IsWellTyped ctx b ty := by
  induction red generalizing ty with
  | nil => assumption
  | cons _ _ _ _ _ ih =>
    apply ih
    apply det_reduction
    assumption
    assumption

-- all terms are closed, and have the corresponding type
inductive SubstAll : List LamType -> List Term -> Prop where
| nil : SubstAll [] []
| cons
  (ty: LamType) (ctx: List LamType)
  (term: Term) (terms: List Term) :
  IsWellTyped [] term ty ->
  SubstAll ctx terms ->
  SubstAll (ty::ctx) (term::terms)

-- all terms are closed, and have the corresponding type
def subst_all (term: Term) (wt: IsWellTyped ctx term ty)
  (args: List Term) (hctx: SubstAll ctx args) : IsWellTyped [] (Term.subst_all 0 term args) ty := by
  induction hctx generalizing term with
  | nil => assumption
  | cons arg_ty ctx arg args harg _ ih =>
    apply ih
    apply IsWellTyped.subst_closed_term
    assumption
    assumption

def from_closed_term (wt: IsWellTyped [] term ty) : IsWellTyped ctx term ty := by
  rw [←List.append_nil ctx]
  rw [←Term.weakenN_closed term ctx.length]
  apply weakenN
  assumption
  apply closed (ctx := [])
  assumption

end IsWellTyped

def DetHeredHalts (term: Term) (h: IsWellTyped ctx term ty) : Prop :=
  match ty with
  | .void => False
  | .func arg_ty ret_ty =>
    term.DetHalts ∧
    ∀{arg: Term} (ha: IsWellTyped ctx arg arg_ty),
    DetHeredHalts arg ha ->
    DetHeredHalts (.app term arg) (.app ctx term arg arg_ty ret_ty h ha)

namespace DetHeredHalts

def Halts {term} {h: IsWellTyped ctx term ty} (h: DetHeredHalts term h) : term.DetHalts := by
  cases ty
  contradiction
  exact h.left

def reduce (r: DetReductionStep term term') (wt: IsWellTyped [] term ty) : DetHeredHalts term wt ↔ DetHeredHalts term' (IsWellTyped.det_reduction r wt) := by
  induction ty generalizing term term' with
  | void => simp [DetHeredHalts]
  | func arg_ty ret_ty iha ihr =>
    apply Iff.intro
    · intro ⟨h₀, h⟩
      apply And.intro
      rwa [←r.halts]
      intro arg arg_wt ha
      have r' := DetReductionStep.app_func term term' arg r
      rw [←ihr r']
      apply h
      assumption
      apply IsWellTyped.app
      assumption
      assumption
    · intro ⟨h₀, h⟩
      apply And.intro
      rwa [r.halts]
      intro arg arg_wt ha
      have r' := DetReductionStep.app_func term term' arg r
      rw [ihr r']
      apply h
      assumption

def reduce_to (r: DetReduction term term') (wt: IsWellTyped [] term ty) : DetHeredHalts term wt ↔ DetHeredHalts term' (IsWellTyped.preservation r wt) := by
  induction r with
  | nil => apply Iff.rfl
  | cons a b c ab bc ih =>
    rw [←ih]
    apply reduce
    assumption
    apply IsWellTyped.det_reduction
    assumption
    assumption

-- all terms are closed, and have the corresponding type
inductive SubstAll : List LamType -> List Term -> Prop where
| nil : SubstAll [] []
| cons
  (ty: LamType) (ctx: List LamType)
  (term: Term) (terms: List Term)
  (wt: IsWellTyped [] term ty):
  DetHeredHalts term wt ->
  SubstAll ctx terms ->
  SubstAll (ty::ctx) (term::terms)

def subst_all_length_eq (subst: DetHeredHalts.SubstAll ctx args) : ctx.length = args.length := by
  induction subst with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

def SubstAll.getElem_IsWellTyped {ctx: List LamType} {args: List Term} (index: Nat) (subst: SubstAll ctx args) (h: index < args.length) :
  SimplyTyped.IsWellTyped [] args[index] (ctx[index]'(by rwa [subst_all_length_eq subst])) := by
  induction subst generalizing index with
  | nil => contradiction
  | cons ctx_ty ctx arg args arg_wt arg_halts subst ih =>
    cases index
    simp; assumption
    simp; apply ih

def SubstAll.getElem_DetHeredHalts (index: Nat) (subst: SubstAll ctx args) (h: index < args.length) :
  DetHeredHalts _ (subst.getElem_IsWellTyped index h) := by
  induction subst generalizing index with
  | nil => contradiction
  | cons ctx_ty ctx arg args arg_wt arg_halts subst ih =>
    cases index
    simp; assumption
    simp; apply ih

private def subst_all_var
  (ctx: List LamType) (args: List Term)
  (subst: DetHeredHalts.SubstAll ctx args)
  (wt: IsWellTyped ctx (.var index) ty)
  : Term.subst_all 0 (.var index) args = args[index]'(by
    cases wt
    rwa [←subst_all_length_eq subst]) := by
  cases wt with
  | var _ _ index_lt =>
  subst ty
  induction args generalizing index ctx with
  | nil =>
    rw [subst_all_length_eq subst] at index_lt
    contradiction
  | cons arg args ih =>
    unfold Term.subst_all
    cases subst with
    | cons ctx_ty ctx _ _ arg_wt args_halts subst =>
    cases index
    simp [Term.subst, Term.subst_all_closed _ _ arg_wt.closed]
    simp [Term.subst]
    apply ih
    assumption
    apply Nat.lt_of_succ_lt_succ
    assumption

private def subst_all_app
  (ctx: List LamType)
  (func arg: Term)
  (args: List Term)
  (subst: DetHeredHalts.SubstAll ctx args)
  (wt: IsWellTyped ctx (func.app arg) ty)
  : Term.subst_all 0 (func.app arg) args =
  (Term.subst_all 0 func args).app (Term.subst_all 0 arg args) := by
  cases wt with
  | app _ _ _ arg_ty _ func_wt arg_wt =>
  induction args generalizing ctx func arg with
  | nil => rfl
  | cons arg args ih =>
    unfold Term.subst_all
    rw [Term.subst]
    cases subst with
    | cons ctx_ty ctx _ _ arg'_wt arg'_halts subst =>
    apply ih
    assumption
    apply IsWellTyped.subst
    assumption
    apply IsWellTyped.from_closed_term
    assumption
    apply IsWellTyped.subst
    assumption
    apply IsWellTyped.from_closed_term
    assumption

private def subst_all_lam
  (ctx: List LamType)
  (body: Term)
  (args: List Term)
  (subst: DetHeredHalts.SubstAll ctx args)
  (wt: IsWellTyped ctx body.lam ty)
  : Term.subst_all 0 body.lam args =
  (Term.subst_all 1 body args).lam := by
  induction subst generalizing body with
  | nil => rfl
  | cons ctx_ty ctx arg args arg_wt arg_halts subst ih =>
    unfold Term.subst_all
    simp [Term.subst]
    rw [ih]
    congr
    rw [Term.weaken_closed _ _ arg_wt.closed]
    apply wt.subst
    exact IsWellTyped.from_closed_term arg_wt

def subst_all
  (term: Term) (args: List Term) (wt: IsWellTyped ctx term ty)
  (subst: DetHeredHalts.SubstAll ctx args) :
  DetHeredHalts (term.subst_all 0 args) (IsWellTyped.subst_all term wt args subst.IsWellTyped) := by
  induction term generalizing ctx ty with
  | var index =>
    conv => { lhs; rw [subst_all_var (subst := subst) (wt :=  wt)] }
    cases wt with
    | var _ _ index_lt =>
    subst ty
    apply SubstAll.getElem_DetHeredHalts (subst := subst)
  | app func arg func_ih arg_ih =>
    conv => { lhs; rw [subst_all_app (subst := subst) (wt :=  wt)] }
    cases wt with
    | app  _ _ _ arg_ty _ func_wt arg_wt =>
    apply (func_ih (ty := LamType.func _ _) _ _).right
    apply arg_ih
    repeat assumption
  | lam body body_ih =>
    cases wt with
    | lam _ _ arg_ty ret_ty wt  =>
    apply And.intro
    · apply Term.DetHalts.mk
      apply Term.IsValue.lam (body.subst_all 1 args)
      rw [subst_all_lam (wt := .lam _ _ _ _ wt) (subst := subst)]
      apply DetReduction.nil
    · intro arg arg_wt h
      conv => { lhs; rw [subst_all_lam (wt := .lam _ _ _ _ wt) (subst := subst)] }
      sorry

def of_well_typed (term: Term) (wt: IsWellTyped [] term ty) : DetHeredHalts term wt := by
  apply subst_all (ctx := []) (term := term) (args := [])
  assumption
  apply SubstAll.nil

end DetHeredHalts

def halts_of_well_typed (term: Term) (wt: IsWellTyped [] term ty) : term.DetHalts := (DetHeredHalts.of_well_typed term wt).Halts

end SimplyTyped

end LambdaCalc
