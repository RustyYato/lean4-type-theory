namespace LambdaCalc

-- a term in the lambda calculus, where variables are represented using debuijin inidices
inductive Term where
| var (index: Nat)
| lam (body: Term)
| app (func arg: Term)

namespace Term

inductive IsClosedAt : Term -> Nat -> Prop where
| var (index: Nat) (binders: Nat) : index < binders -> IsClosedAt (.var index) binders
| lam (body: Term) (binders: Nat) : IsClosedAt body (binders + 1) -> IsClosedAt (.lam body) binders
| app (func arg: Term) (binders: Nat) :
  IsClosedAt func binders ->
  IsClosedAt arg binders ->
  IsClosedAt (.app func arg) binders

inductive IsValue : Term -> Prop where
| lam (body: Term) : IsValue (.lam body)

def weaken (pos: Nat := 0) : Term -> Term
| .var index => .var <| if index < pos then index else index + 1
| .app func arg => .app (func.weaken pos) (arg.weaken pos)
| .lam body => .lam (body.weaken (pos + 1))

def subst (pos: Nat) (repl: Term) : Term -> Term
| .var index =>
  if index = pos then repl
  else .var <| if index < pos then index else index - 1
| .app func arg => .app (subst pos repl func) (subst pos repl arg)
| .lam body => .lam (subst (pos + 1) repl.weaken body)

def weaken_closed_at
  (a b: Nat)
  (term: Term)
  (h: a <= b) : term.IsClosedAt a -> Term.weaken b term = term := by
  intro closed
  induction closed generalizing b with
  | var index a g =>
    unfold weaken
    rw [if_pos]
    exact trans g h
  | app _ _ _ _ _ iha ihb =>
    unfold weaken
    congr
    apply iha
    assumption
    apply ihb
    assumption
  | lam _ _ _ ih =>
    unfold weaken
    congr
    apply ih
    apply Nat.succ_le_succ
    assumption

def subst_closed_at
  (a b: Nat)
  (term repl: Term)
  (h: a <= b) : term.IsClosedAt a -> Term.subst b repl term = term := by
  intro closed
  induction closed generalizing b repl with
  | var index a g =>
    unfold subst
    rw [if_neg, if_pos]
    exact trans g h
    rintro rfl
    exact Nat.not_lt_of_le h g
  | app _ _ _ _ _ iha ihb =>
    unfold subst
    congr
    apply iha
    assumption
    apply ihb
    assumption
  | lam _ _ _ ih =>
    unfold subst
    congr
    apply ih
    apply Nat.succ_le_succ
    assumption

def weaken_closed (a: Nat) (term: Term) : term.IsClosedAt 0 -> Term.weaken a term = term := by
  intro h
  apply weaken_closed_at
  apply Nat.zero_le
  assumption

def subst_closed (a: Nat) (term repl: Term) : term.IsClosedAt 0 -> Term.subst a repl term = term := by
  intro h
  apply subst_closed_at
  apply Nat.zero_le
  assumption

end Term

inductive DetReductionStep : Term -> Term -> Type where
| subst (body arg ret: Term) :
  arg.IsValue ->
  ret = Term.subst 0 arg body ->
  DetReductionStep (.app (.lam body) arg) ret
| app_func (func func' arg: Term) :
  DetReductionStep func func' ->
  DetReductionStep (.app func arg) (.app func' arg)
| app_arg (func arg arg': Term) :
  func.IsValue ->
  DetReductionStep arg arg' ->
  DetReductionStep (.app func arg) (.app func arg')

-- inductive ReductionStep : Term -> Term -> Type where
-- | subst (body arg ret: Term) :
--   arg.IsValue ->
--   ret = Term.subst 0 arg body ->
--   ReductionStep (.app (.lam body) arg) ret
-- | app_func (func func' arg: Term) :
--   ReductionStep func func' ->
--   ReductionStep (.app func arg) (.app func' arg)
-- | app_arg (func arg arg': Term) :
--   ReductionStep arg arg' ->
--   ReductionStep (.app func arg) (.app func arg')

inductive DetReduction : Term -> Term -> Type where
| nil (term: Term) : DetReduction term term
| cons (a b c: Term) : DetReductionStep a b -> DetReduction b c -> DetReduction a c

-- inductive Reduction : Term -> Term -> Type where
-- | nil (term: Term) : Reduction term term
-- | cons (a b c: Term) : ReductionStep a b -> Reduction b c -> Reduction a c

def det_reduction_step_implies_not_value (h: DetReductionStep a b) : ¬a.IsValue := by
  rintro ⟨⟩
  nomatch h

instance : ∀a: Term, Decidable (Term.IsValue a)
| .var _ => .isFalse nofun
| .app _ _ => .isFalse nofun
| .lam _ => .isTrue (Term.IsValue.lam _)

-- there is at most one deterministic reduction step for every value pair of values
instance : Subsingleton (Σb, DetReductionStep a b) where
  allEq := by
    intro ⟨b₀, x⟩ ⟨b₁, y⟩
    induction x generalizing b₁ with
    | subst _ _ ret =>
      subst ret
      cases y
      subst b₁
      rfl
      exfalso
      have := det_reduction_step_implies_not_value (by assumption) (Term.IsValue.lam _)
      contradiction
      have := det_reduction_step_implies_not_value (by assumption) (by assumption)
      contradiction
    | app_arg _ _ _ _ _ ih =>
      cases y
      · have := det_reduction_step_implies_not_value (by assumption) (by assumption)
        contradiction
      · have := det_reduction_step_implies_not_value (by assumption) (by assumption)
        contradiction
      · rename_i h
        obtain ⟨rfl, h⟩ := ih _ h
        congr
    | app_func _ _ _ _ ih =>
      cases y
      · have := det_reduction_step_implies_not_value (by assumption) (Term.IsValue.lam _)
        contradiction
      · rename_i h
        obtain ⟨rfl, h⟩ := ih _ h
        congr
      · rename_i h _
        have := det_reduction_step_implies_not_value (by assumption) h
        contradiction

def DetReductionStep.unique {a b c: Term} (ab: DetReductionStep a b) (ac: DetReductionStep a c) : b = c := by
    let x' : Σb', DetReductionStep a b' := ⟨_, ab⟩
    let y' : Σb', DetReductionStep a b' := ⟨_, ac⟩
    have : x' = y' := Subsingleton.allEq _ _
    exact (Sigma.mk.inj this).left

-- there is at most one deterministic reduction step for every value pair of values
instance : Subsingleton (DetReductionStep a b) where
  allEq := by
    intro x y
    let x' : Σb', DetReductionStep a b' := ⟨_, x⟩
    let y' : Σb', DetReductionStep a b' := ⟨_, y⟩
    have : x' = y' := Subsingleton.allEq _ _
    exact eq_of_heq ((Sigma.mk.inj this).right)

-- for any closed lambda calculus term which is not a value, there is always a reduction step we can take
def det_reduction_of_not_value (h: ¬a.IsValue) (g: a.IsClosedAt 0) : Σb, DetReductionStep a b :=
  match a with
  | .var _ => nomatch g
  | .lam _ => nomatch h (Term.IsValue.lam _)
  | .app func arg =>
    if h₀:func.IsValue then
      if h₁:arg.IsValue then
        match func with
        | .lam body => ⟨_, DetReductionStep.subst body arg _ h₁ rfl⟩
      else
        have ⟨arg', red⟩ := det_reduction_of_not_value h₁ (by
          cases g
          assumption)
        ⟨_, DetReductionStep.app_arg _ _ _ h₀ red⟩
    else
        have ⟨arg', red⟩ := det_reduction_of_not_value h₀ (by
          cases g
          assumption)
        ⟨_, DetReductionStep.app_func _ _ _ red⟩

inductive Term.DetHalts (a: Term) : Prop where
| mk (val: Term) (val_sec: val.IsValue) (reduction: DetReduction a val)

def Term.weakenN (term: Term) : Nat -> Term
| 0 => term
| n + 1 => (term.weakenN n).weaken

def Term.weakenN_closed (term: Term) (n: Nat) : term.IsClosedAt 0 -> term.weakenN n = term := by
  intro closed
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold weakenN
    rwa [weaken_closed]
    rwa [ih]

def DetReductionStep.halts (red: DetReductionStep a b) : Term.DetHalts a ↔ Term.DetHalts b := by
  apply Iff.intro
  intro ⟨val, val_spec, val_red⟩
  cases val_red
  nomatch det_reduction_step_implies_not_value red val_spec
  rename_i h _
  cases DetReductionStep.unique red h
  refine ⟨val, ?_, ?_⟩
  assumption
  assumption
  intro ⟨val, val_spec, val_red⟩
  refine ⟨val, ?_, ?_⟩
  assumption
  apply DetReduction.cons
  assumption
  assumption

def Term.subst_all (n : Nat := 0) (term: Term) : List Term -> Term
| [] => term
| repl::repls => Term.subst_all n (Term.subst n repl term) repls

def Term.subst_all_closed (term: Term) (args: List Term) (h: term.IsClosedAt 0) : term.subst_all 0 args = term := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
    unfold Term.subst_all
    rwa [Term.subst_closed]
    assumption

def DetReduction.app_arg
  (func arg arg': Term) (func_val: func.IsValue) :
  DetReduction arg arg' ->
  DetReduction (func.app arg) (func.app arg')
| .nil _ => .nil _
| .cons a b c ab bc =>
  .cons (func.app a) (func.app b) (func.app c) (.app_arg _ _ _ func_val ab) (.app_arg _ _ _ func_val bc)

def Term.subst_0_commutes_subst_1 (term: Term) :
  Term.subst 0 a (Term.subst 1 b term) = Term.subst 0 b (Term.subst 0 a term) := by
  sorry

def Term.subst_0_commutes_subst_all_1 (term: Term) :
  Term.subst 0 a (Term.subst_all 1 term args) = Term.subst_all 0 (Term.subst 0 a term) args := by
  sorry

end LambdaCalc
