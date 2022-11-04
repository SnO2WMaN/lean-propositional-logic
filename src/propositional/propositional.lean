import tactic 
import propositional.language

universe u

namespace prop

variables (A : Type u)

inductive ProofCL (Γ : set Formula): set Formula
| ctx : ∀ {φ}, φ ∈ Γ → ProofCL φ
| P1  : ∀ {φ ψ}, ProofCL $ φ →' (ψ →' φ)
| P2  : ∀ {φ ψ χ}, ProofCL $ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ))
| P3  : ∀ {φ ψ}, ProofCL $ (¬'φ →' ¬'ψ) →' (ψ →' φ)
| mp  : ∀ {φ ψ}, ProofCL (φ →' ψ) → ProofCL φ → ProofCL ψ

-- notation `𝐂𝐋` := ProofCL

infix ` ⊢ ` :25 := ProofCL 
notation `⊢ ` φ :25 := ∅ ⊢ φ

-- def consistent (Γ) : Prop := ⊥' ∉ (𝐂𝐋 Γ) 
-- def inconsistent (Γ) := ¬(consistent Γ)

open ProofCL

lemma ident (Γ φ) : Γ ⊢ (φ →' φ) :=
begin
  have h₁ := @ProofCL.P2 Γ φ (φ →' φ) φ,
  have h₂ := @ProofCL.P1 Γ φ (φ →' φ),
  have h₃ := @ProofCL.P1 Γ φ φ,
    
  have h₄ := @mp _ _ _ h₁ h₂,
  have h₅ := @mp _ _ _ h₄ h₃,
  assumption,
end

lemma negneg (Γ φ) : (Γ ⊢ ¬'¬'φ) ↔ (Γ ⊢ φ) :=
begin
  split,
  admit,
  admit,
end

theorem expand_context (Γ φ ψ) : (Γ ⊢ ψ) → (Γ ∪ {φ} ⊢ ψ) :=
begin
  intro h,
  induction h,
  case ctx : {
    apply @ProofCL.ctx (Γ ∪ {φ}),
    finish,
  },
  case P1 : {
    apply @ProofCL.P1 (Γ ∪ {φ}),
  },
  case P2 : {
    apply @ProofCL.P2 (Γ ∪ {φ}),
  },
  case P3 : {
    apply @ProofCL.P3 (Γ ∪ {φ}),
  },
  case mp : _ _ _ _ h₁ h₂ {
    apply @ProofCL.mp (Γ ∪ {φ}) _ _ h₁ h₂,
  },
end

lemma append (Γ φ ψ) : (Γ ⊢ ψ) → (Γ ⊢ φ →' ψ) := 
begin
  admit,
end

theorem deduction (Γ φ ψ) : (Γ ∪ {φ} ⊢ ψ) → (Γ ⊢ (φ →' ψ)) :=
begin
  intro h,
  induction h,
  case ctx : a b {
    simp at *,
    cases b,
    { rw b, exact ident Γ φ, },
    {
      sorry,
    },
  },
  case P1 : φi ψi {
    -- exact @ProofCL.P1 Γ φ (φi →' ψi),
    sorry,
  },
  {sorry,},
  {sorry,},
  {sorry,},
end

theorem deduction' (Γ φ ψ) : (Γ ⊢ (φ →' ψ)) → (Γ ∪ {φ} ⊢ ψ) :=
begin
  intro h,
  -- assume h₂,
  -- apply (@append Γ φ ψ) h,
  admit,
end

example (φ ψ) : (⊢ φ →' ψ) → ({φ} ⊢ ψ) := 
begin
  intro h,
  have h₁ := (@deduction' ∅ φ ψ) h, 
  rw set.empty_union at h₁,
  assumption,
end

def inconsistent (Γ) := Γ ⊢ ⊥'
def consistent (Γ) := ¬(inconsistent Γ)

lemma inconsistent_explosion (Γ φ) : (inconsistent Γ) → (Γ ⊢ φ) :=
begin
  intro h,
  admit,
end

lemma lemma_2_10 (Γ φ) : (Γ ⊢ φ) → (Γ ⊢ ¬'φ) → (inconsistent Γ) :=
begin
  intros hp hnp,
  have h₂ := deduction' _ _ _ hnp,
  have h₃ : inconsistent (Γ ∪ {φ}) := h₂,
end

lemma lemma_2_10' (Γ φ) : consistent Γ → (¬(Γ ⊢ φ)) ∨ (¬(Γ ⊢ ¬'φ)) :=
begin
  contrapose,
  rw push_neg.not_or_eq,
  repeat { rw not_not },
  intro h,
  have h4 := @lemma_2_10 Γ φ (h.elim_left) (h.elim_right),
  finish,
end


lemma lemma_2_11 (Γ φ) : (inconsistent (Γ ∪ {¬'φ})) ↔ (Γ ⊢ φ) :=
begin
  split,
  intro h,
  have h₂ := (@deduction Γ (¬'φ) ⊥') h,
  exact iff.elim_left (negneg Γ φ) h₂,

  intro h,
  apply deduction',
  apply iff.elim_right (negneg Γ φ),
  assumption,
end

lemma lemma_2_12 (Γ φ) : consistent Γ → (consistent (Γ ∪ {φ})) ∨ (consistent (Γ ∪ {¬'φ})) :=
begin
  contrapose,
  rw push_neg.not_or_eq,
  intro h,
  have hl : inconsistent (Γ ∪ {φ}) := by finish, 
  have hr : inconsistent (Γ ∪ {¬'φ}) := by finish,
  have h₂ := (iff.elim_left (@lemma_2_11 Γ φ)) hr,
  have h₃ := sorry,
  have h₄ := lemma_2_10 Γ φ h₂ h₃,
  finish,
end

def satisfy (v : ℕ → Prop) : Formula → Prop
| (Formula.var p) := v p
| ⊥'              := false
| (φ →' ψ)        := (satisfy φ) → (satisfy ψ)

def models (v : ℕ → Prop) (φ : Formula) : Prop := satisfy v φ
infix `⊧` :25 := models

def valid (φ) := ∀ v, v ⊧ φ
prefix `⊧` :25 := valid

lemma valid_P1 (φ ψ) : ⊧ (φ →' ψ →' φ) := 
begin
  intro v,
  intros h₁ _,
  assumption,
end

lemma valid_P2 (φ ψ χ) : ⊧ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ)) := 
begin
  intro v,
  intros h₁ h₂ h₃,
  exact (h₁ h₃) (h₂ h₃),
end

lemma valid_P3 (φ ψ) : ⊧ (¬'φ →' ¬'ψ) →' (ψ →' φ) := 
begin
  intro v,
  intros h₁ h₂,
  by_contradiction h₃,
  solve_by_elim, -- TODO:
end

lemma valid_mp (φ ψ) : (⊧ φ →' ψ) → (⊧ φ) → (⊧ ψ) :=
begin
  intros h₀ h₁ v,
  exact (h₀ v) (h₁ v),
end

theorem soundness (Γ φ) : (Γ ⊢ φ) → (⊧ φ) :=
begin
  intro h,
  induction h,
  {sorry,},
  {exact @valid_P1 _ _,},
  {exact @valid_P2 _ _ _},
  {exact @valid_P3 _ _},
  case mp: _ _ _ _ h₁ h₂ {exact @valid_mp _ _ h₁ h₂,},
end

theorem completeness (Γ φ) : ⊧φ → (Γ ⊢ φ) :=
begin
  intro hM,
  sorry,
end

end prop