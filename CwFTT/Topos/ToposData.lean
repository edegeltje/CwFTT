import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

universe v u
namespace CategoryTheory

/-- `ToposData₁` contains the data of -/
class ToposData (C : Type u) [Category.{v} C] where
  -- an elementary topos has
  /-- A choice of classifier, with -/
  Ω : Classifier C
  /-- A choice of binary products and terminal object -/
  [cartesianMonoidal : CartesianMonoidalCategory C]
  /-- A choice of exponential objects -/
  exps : ∀ (X : C), Closed X
  /-- A choice of representation of a subobject for each predicate -/
  subobjects : ChosenPullbacksAlong (Ω.truth)

variable {C : Type u} [Category.{v} C]
namespace ToposData
open Limits

section equalizer

/--
Given choices of subobjects for all predicates, and choices of products,
we can construct(!) equalizers by taking the subobject of `X` corresponding to
the predicate `⟨f,g⟩ ≫ «=» : X ⟶ Ω` (corresponding to `fun x => f x = g x` in Set)
-/
protected def equalizer (data : ToposData C) {X Y : C} (f g : X ⟶ Y) : C :=
  letI := data.cartesianMonoidal
  -- letI := data.subobjects
  data.subobjects.pullbackObj (data.cartesianMonoidal.lift f g ≫ data.Ω.χ
    (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y))) data.Ω.truth

/-- the equalizing morphism for the topos-construction of pullbacks -/
protected def equalizer.ι (data : ToposData C) {X Y : C} (f g : X ⟶ Y) :
    data.equalizer f g ⟶ X :=
  data.subobjects.fst
    (data.cartesianMonoidal.lift f g ≫
      data.Ω.χ (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y)))
    (data.Ω.truth)

lemma equalizer.condition [data : ToposData C] {X Y : C} (f g : X ⟶ Y) :
  ToposData.equalizer.ι data f g ≫ f = ToposData.equalizer.ι data f g ≫ g := by
  let := data.cartesianMonoidal
  let := data.subobjects
  obtain ⟨⟨w⟩,⟨h⟩⟩ := (data.Ω.isPullback (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y)))
  have : IsPullback (equalizer.ι data f g)
      (PullbackCone.IsLimit.lift h (equalizer.ι data f g ≫ (data.cartesianMonoidal.lift f g))
        (data.subobjects.snd _ _) (by
          simpa [-CartesianMonoidalCategory.comp_lift] using data.subobjects.condition))
      (data.cartesianMonoidal.lift f g)
      (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y)) := by
    refine IsPullback.of_bot ?_ (by
        simp only [PullbackCone.mk_pt]
        generalize_proofs _ h1 h2
        simpa using (PullbackCone.IsLimit.lift_fst h _ _ h2).symm)
      (data.Ω.isPullback (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y)))
    convert data.subobjects.isPullback _ _
    simpa using (PullbackCone.IsLimit.lift_snd h _ _ _)
  nth_rw 6 [← CartesianMonoidalCategory.lift_snd f g]
  nth_rw 4 [← CartesianMonoidalCategory.lift_fst f g]
  simp_rw [this.w_assoc, data.cartesianMonoidal.lift_fst,
    data.cartesianMonoidal.lift_snd]

private def equalizer.η [data : ToposData C] {X Y : C} (f g : X ⟶ Y) :
  data.equalizer f g ⟶ Y := equalizer.ι data f g ≫ f

private lemma equalizer._isPullback_1 [data : ToposData C] {X Y : C} (f g : X ⟶ Y) :
    IsPullback (equalizer.ι data f g) (equalizer.η f g ≫ data.Ω.χ₀ _)
      (data.cartesianMonoidal.lift f g ≫ data.Ω.χ (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y)))
      (data.Ω.truth) := by
  convert data.subobjects.isPullback _ _
  exact Subsingleton.elim _ _

private lemma equalizer._isPullback_2 [data : ToposData C] {X Y : C} (f g : X ⟶ Y) :
    IsPullback (equalizer.ι data f g) (equalizer.η f g)
      (data.cartesianMonoidal.lift f g)
      (data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y)) := by
  apply IsPullback.of_bot (_isPullback_1 f g) _ (data.Ω.isPullback _)
  apply data.cartesianMonoidal.hom_ext <;> simp [η, ← equalizer.condition]

abbrev equalizer.mkFork (data : ToposData C) {X Y : C} (f g : X ⟶ Y) : Fork f g :=
  .ofι _ (equalizer.condition f g)

def equalizer.lift (data : ToposData C) {X Y : C} {f g : X ⟶ Y}
    {Z : C} (h : Z ⟶ X) (heq : h ≫ f = h ≫ g := by cat_disch) : Z ⟶ data.equalizer f g := by
  apply data.subobjects.lift h (h ≫ f ≫ data.Ω.χ₀ _) _
  have : h ≫ data.cartesianMonoidal.lift f g = h ≫ f ≫ data.cartesianMonoidal.lift (𝟙 Y) (𝟙 Y) := by
    apply data.cartesianMonoidal.hom_ext <;> simp [heq]
  rw [reassoc_of% this,Category.assoc, Category.assoc,
    (data.Ω.isPullback _).w]

@[reassoc (attr := simp)]
lemma equalizer.lift_ι [data : ToposData C] {X Y : C} {f g : X ⟶ Y}
    {Z : C} (h : Z ⟶ X) (heq : h ≫ f = h ≫ g) :
    equalizer.lift data h heq ≫ equalizer.ι data f g = h := by
  simp [lift,equalizer.ι]

lemma equalizer.hom_ext [data : ToposData C] {X Y : C} {f g : X ⟶ Y} {Z : C}
    {h₁ h₂ : Z ⟶ data.equalizer f g} (heq : h₁ ≫ equalizer.ι data f g = h₂ ≫ equalizer.ι data f g) :
    h₁ = h₂ := by
  apply (equalizer._isPullback_1 f g).hom_ext
  · exact heq
  · exact Subsingleton.elim _ _

def equalizer.isLimit (data : ToposData C) {X Y : C} (f g : X ⟶ Y) :
    (IsLimit (ToposData.equalizer.mkFork data f g)) :=
  Fork.IsLimit.mk _ (fun s => lift data s.ι s.condition)
    (fun s => lift_ι s.ι s.condition)
    (fun s m hm => equalizer.hom_ext (by simpa [lift_ι]))

end equalizer
section pullback

def pullback (data : ToposData C) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : C :=
  data.equalizer (data.cartesianMonoidal.fst X Y ≫ f) (data.cartesianMonoidal.snd X Y ≫ g)

def pullback.fst [data : ToposData C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  data.pullback f g ⟶ X := ToposData.equalizer.ι data _ _ ≫ data.cartesianMonoidal.fst _ _

def pullback.snd [data : ToposData C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  data.pullback f g ⟶ Y := ToposData.equalizer.ι data _ _ ≫ data.cartesianMonoidal.snd _ _

def pullback.condition [data : ToposData C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  simp [fst, snd, equalizer.condition]

abbrev pullback.pullbackCone (data : ToposData C) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  PullbackCone f g := .mk _ _ (pullback.condition)

def pullback.lift (data : ToposData C) {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (w : fst ≫ f = snd ≫ g := by cat_disch) :
    W ⟶ data.pullback f g :=
  equalizer.lift data (data.cartesianMonoidal.lift fst snd)

@[reassoc (attr := simp)]
lemma pullback.lift_fst [data : ToposData C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (w : fst ≫ f = snd ≫ g) :
    lift data _ _ w ≫ pullback.fst f g = fst := by
  simp [lift, pullback.fst]

@[reassoc (attr := simp)]
lemma pullback.lift_snd [data : ToposData C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (w : fst ≫ f = snd ≫ g) :
    lift data _ _ w ≫ pullback.snd f g = snd := by
  simp [lift, pullback.snd]

lemma pullback.hom_ext [data : ToposData C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {W : C} (h₁ h₂ : W ⟶ data.pullback f g) (hfst : h₁ ≫ pullback.fst f g = h₂ ≫ pullback.fst f g)
    (hsnd : h₁ ≫ pullback.snd f g = h₂ ≫ pullback.snd f g) :
    h₁ = h₂ := by
  apply equalizer.hom_ext
  apply data.cartesianMonoidal.hom_ext <;> simpa

def pullback.isLimit (data : ToposData C) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (pullback.pullbackCone data f g) :=
  PullbackCone.IsLimit.mk _
    (fun s => lift data s.fst s.snd s.condition)
    (fun s => lift_fst s.fst s.snd s.condition)
    (fun s => lift_snd s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ => pullback.hom_ext _ _ (by simpa) (by simpa))


end pullback

-- def ofChoice [HasFiniteLimits C] [HasClassifier C]

end ToposData
end CategoryTheory
