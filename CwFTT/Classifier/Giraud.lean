import Mathlib

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]
open Limits

abbrev Rel (X : C) := BinaryFan X X

namespace Rel

def IsReflexive {X : C} (R : Rel X) : Prop := ∃ f : X ⟶ R.pt, f ≫ R.fst = 𝟙 X ∧ f ≫ R.snd = 𝟙 X

lemma isReflexive_iff {X : C} (R : Rel X) : R.IsReflexive ↔
    ∃ f : X ⟶ R.pt, f ≫ R.fst = 𝟙 X ∧ f ≫ R.snd = 𝟙 X := Iff.rfl

def IsSymmetric {X : C} (R : Rel X) : Prop :=
  ∃ f : R.pt ⟶ R.pt, f ≫ R.fst = R.snd ∧ f ≫ R.snd = R.fst

lemma isSymmetric_iff {X : C} (R : Rel X) : R.IsSymmetric ↔
  ∃ f : R.pt ⟶ R.pt, f ≫ R.fst = R.snd ∧ f ≫ R.snd = R.fst := Iff.rfl

def IsTransitive {X : C} (R : Rel X) : Prop := ∀ Y : C, ∀ fst : Y ⟶ R.pt, ∀ snd : Y ⟶ R.pt,
  fst ≫ R.snd = snd ≫ R.fst → ∃ f : Y ⟶ R.pt, f ≫ R.fst = fst ≫ R.fst ∧ f ≫ R.snd = snd ≫ R.snd

-- lemma isTransitive_iff_of_hasPullback {X : C} (R : Rel X) [HasPullback R.fst R.snd] :


lemma isTransitive_iff {X : C} (R : Rel X) : R.IsTransitive ↔
    ∀ Y : C, ∀ fst : Y ⟶ R.pt, ∀ snd : Y ⟶ R.pt,
      fst ≫ R.snd = snd ≫ R.fst → ∃ f : Y ⟶ R.pt, f ≫ R.fst = fst ≫ R.fst ∧
      f ≫ R.snd = snd ≫ R.snd := Iff.rfl

@[mk_iff]
structure IsEquivalence {X : C} (R : Rel X) : Prop where
  isReflexive : IsReflexive R
  isSymmetric : IsSymmetric R
  isTransitive : IsTransitive R

attribute [simp] isEquivalence_iff
-- #check IsPullback.condition
def IsEffective {X : C} (R : Rel X) : Prop := ∃ Y, ∃ f : X ⟶ Y, IsKernelPair f R.fst R.snd

lemma isEffective_iff {X : C} (R : Rel X) : R.IsEffective ↔
    ∃ Y, ∃ f : X ⟶ Y, IsKernelPair f R.fst R.snd := Iff.rfl


lemma IsReflexive.of_isEffective {X : C} {R : Rel X} (hR : R.IsEffective) : R.IsReflexive:= by
  obtain ⟨Y,f,hf⟩ := hR
  rw [isReflexive_iff]
  use (hf.lift (𝟙 _) (𝟙 _) (by simp))
  simp

lemma IsSymmetric.of_isEffective {X : C} {R : Rel X} (hR : R.IsEffective) : R.IsSymmetric := by
  obtain ⟨Y,f,hf⟩ := hR
  rw [isSymmetric_iff]
  use (hf.lift (R.snd) (R.fst) (hf.w.symm))
  simp

lemma IsTransitive.of_isEffective {X : C} {R : Rel X} (hR : R.IsEffective) : R.IsTransitive := by
  obtain ⟨Y,f,hf⟩ := hR
  rw [isTransitive_iff]
  intro Y fst snd condition
  use (hf.lift (fst ≫ R.fst) (snd ≫ R.snd)
    (by simp_rw [Category.assoc, hf.w,reassoc_of% condition,hf.w]))
  simp

end Rel


def MorphismProperty.effectiveEpis : MorphismProperty C := fun _ _ f => EffectiveEpi f

lemma MorphismProperty.effectiveEpis_apply :
  ∀ (X Y : C) (f : X ⟶ Y), effectiveEpis f ↔ EffectiveEpi f := by intros; rfl

noncomputable section

variable (C) in
@[mk_iff]
class IsGiraud where
  [isLocallyPresentable : IsLocallyPresentable.{u} C]
  isUniversalColimit_of_isColimit {J : Type v} [Category.{v,v} J]
    {f : J ⥤ C} {s : Cocone f} (hs : IsColimit s) : IsUniversalColimit s
  coproductDisjoint {ι : Type v} (f : ι → C) : Limits.CoproductDisjoint f
  isEffective_of_isEquivalence : ∀ X : C, ∀ R : Rel X, R.IsEquivalence → R.IsEffective

attribute [instance] IsGiraud.isLocallyPresentable

-- variable [IsLocallyPresentable C] in
-- #synth HasCoproducts C

variable (C)

def IsGiraud.cardinal [IsGiraud C] : Cardinal := by
  have : IsAccessibleCategory C := inferInstance
  exact this.exists_cardinal.choose

instance IsGiraud.cardinal_isRegular [IsGiraud C] : Fact (IsGiraud.cardinal C).IsRegular :=
  (IsGiraud.cardinal._proof_1 C).exists_cardinal.choose_spec.choose

instance IsGiraud.foo [IsGiraud C] : Fact (IsGiraud.cardinal C).IsRegular :=
  (IsGiraud.cardinal._proof_1 C).exists_cardinal.choose_spec.choose_spec


def IsGiraud.generator [IsGiraud C] : ObjectProperty C := by
  have : IsAccessibleCategory C := inferInstance
  have hX₁ := this.exists_cardinal.choose_spec.choose
  have := (IsGiraud.cardinal._proof_1 C).exists_cardinal.choose_spec.choose_spec.exists_generator
  exact this.choose

lemma IsGiraud.generator_essentiallySmall [IsGiraud C] :
    ObjectProperty.EssentiallySmall.{u,v,u} (IsGiraud.generator C) :=
  (IsGiraud.generator._proof_4 C).choose_spec.choose

lemma IsGiraud.generator_foo [IsGiraud C] :
    (IsGiraud.generator C).IsCardinalFilteredGenerator (IsGiraud.cardinal C) :=
  (IsGiraud.generator._proof_4 C).choose_spec.choose_spec

abbrev IsGiraud.Site [IsGiraud C] : Type u := (IsGiraud.generator C).FullSubcategory

def IsGiraud.topology [IsGiraud C] : GrothendieckTopology (IsGiraud.Site C) where
  sieves X := { S : Sieve X | Epi (Limits.Sigma.desc.{max u v} (β :=
    S.arrows.category) (fun f => f.obj.hom))}
  top_mem' := _
  pullback_stable' := _
  transitive' := _

end


end CategoryTheory
