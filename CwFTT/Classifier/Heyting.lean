import CwFTT.Classifier.Ops

universe v u
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

instance (𝒞 : Classifier C) (X : C) : LE (X ⟶ 𝒞.Ω) where
  le f g := CartesianMonoidalCategory.lift f g ≫ 𝒞.and = f

lemma Classifier.le_def (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
  f ≤ g ↔ (CartesianMonoidalCategory.lift f g ≫ 𝒞.and = f) := Iff.rfl

instance [HasPullbacks C] (𝒞 : Classifier C) (X : C) : PartialOrder (X ⟶ 𝒞.Ω) where
  le_refl a := by -- 𝒞.and is co-diagonal(?)
    rw [𝒞.le_def, ← 𝒞.χ_pullback_fst a,← 𝒞.χ_pullback (f₁ := 𝟙 _) (f₂ := 𝟙 _)]
    · simp
    · exact .of_vert_isIso_mono (snd := 𝟙 _) (f := pullback.fst a 𝒞.truth) (by simp)
  le_trans a b c hab hbc := by -- 𝒞.and is associative
    rw [Classifier.le_def] at hab hbc ⊢
    nth_rw 1 2 [← hab,𝒞.and_assoc,hbc]
  le_antisymm a b hab hba := by -- 𝒞.and is commutative
    rw [← hab,𝒞.and_comm,hba]

noncomputable instance [HasPullbacks C] (𝒞 : Classifier C) (X : C) :
    SemilatticeInf (X ⟶ 𝒞.Ω) where
  inf f g := (CartesianMonoidalCategory.lift f g) ≫ 𝒞.and
  inf_le_left f g := by
    rw [𝒞.le_def, 𝒞.and_comm f g, 𝒞.and_assoc, le_refl f]
  inf_le_right f g := by
    rw [𝒞.le_def, 𝒞.and_assoc, le_refl g]
  le_inf a b c hab hac := by
    rw [𝒞.le_def,← 𝒞.and_assoc,hab,hac]

instance [HasFiniteLimits C] (𝒞 : Classifier C) (X : C) :
    Lattice (X ⟶ 𝒞.Ω) where
  sup f g := (CartesianMonoidalCategory.lift f g) ≫ 𝒞.or
  le_sup_left := _
  le_sup_right := _
  sup_le := _

example [HasFiniteLimits C] (𝒞 : Classifier C) (X : C) : HeytingAlgebra (X ⟶ 𝒞.Ω) where
  sup := _
  le_sup_left := _
  le_sup_right := _
  sup_le := _
  inf := _
  inf_le_left := _
  inf_le_right := _
  le_inf := _
  top := _
  le_top := _
  himp := _
  le_himp_iff := _
  bot := _
  bot_le := _
  compl := _
  himp_bot := _



end CategoryTheory
