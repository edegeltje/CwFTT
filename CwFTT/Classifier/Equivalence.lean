import Mathlib.CategoryTheory.Topos.Classifier

universe v₁ v₂ v₃ u₁ u₂ u₃
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- The unique morphism between classifiers mapping each others characteristic maps -/
def Classifier.hom (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ⟶ 𝒞₂.Ω := 𝒞₂.χ (𝒞₁.truth)

@[simp]
lemma Classifier.hom_comp_hom (𝒞₁ 𝒞₂ 𝒞₃ : Classifier C) : 𝒞₁.hom 𝒞₂ ≫ 𝒞₂.hom 𝒞₃ = 𝒞₁.hom 𝒞₃ :=
  𝒞₃.uniq _ <| (𝒞₂.isPullback _).paste_vert (𝒞₃.isPullback _)

@[simp]
lemma Classifier.hom_refl (𝒞₁ : Classifier C) : 𝒞₁.hom 𝒞₁ = 𝟙 _ :=
  (𝒞₁.uniq (χ₀' := 𝟙 _) (𝒞₁.truth) (IsPullback.of_id_snd)).symm

@[simp]
lemma Classifier.χ_comp_hom {𝒞₁ 𝒞₂ : Classifier C} {X Y : C} (m : X ⟶ Y) [Mono m] :
    𝒞₁.χ m ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ m :=
  𝒞₂.uniq m ((𝒞₁.isPullback m).paste_vert (𝒞₂.isPullback (𝒞₁.truth)))

/-- a concrete equivalence of any two subobject classifiers -/
@[simps]
def Classifier.uniqueUpToIso (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ≅ 𝒞₂.Ω where
  hom := 𝒞₁.hom 𝒞₂
  inv := 𝒞₂.hom 𝒞₁
  hom_inv_id := by simp
  inv_hom_id := by simp

-- Classifier.ofRightAdjoint?
-- one would hope to prove that this construction is transitive and reflexive
@[simps]
def Classifier.ofEquivalence (𝒞₁ : Classifier C) (e : C ≌ D) : Classifier D where
  Ω₀ := e.functor.obj 𝒞₁.Ω₀
  Ω := e.functor.obj 𝒞₁.Ω
  truth := e.functor.map 𝒞₁.truth
  mono_truth := inferInstance
  χ₀ Y := e.counitInv.app Y ≫ e.functor.map (𝒞₁.χ₀ (e.inverse.obj Y))
  χ m := (e.counitInv.app _) ≫ e.functor.map (𝒞₁.χ (e.inverse.map m))
  isPullback {F G} m _ := by
    apply ((𝒞₁.isPullback (e.inverse.map m)).map e.functor).of_iso (e.counitIso.app _)
      (e.counitIso.app _) (.refl _) (.refl _) <;> simp
  uniq {F G} m _ := by
    intro χ₀' χ' hχ'
    have : e.inverse.map χ' ≫ e.unitInv.app _ = 𝒞₁.χ (e.inverse.map m) := by
      apply 𝒞₁.uniq (e.inverse.map m) (χ₀' := e.inverse.map χ₀' ≫ e.unitInv.app _)
      exact (hχ'.map (e.inverse)).paste_vert <| IsPullback.of_vert_isIso_mono (by simp)
    simpa using congr(e.counitInv.app G ≫ e.functor.map $this)

/--
Don't use this lemma, ever. instead use Classifier.uniqueUpToIso.
It exists to verify that this construction will have nice defeq properties.
See also Classifier.ofEquivalence_refl
-/
lemma Classifier.ofEquivalence_trans (𝒞₁ : Classifier C) (e₁ : C ≌ D) (e₂ : D ≌ E) :
    (𝒞₁.ofEquivalence e₁).ofEquivalence e₂ = 𝒞₁.ofEquivalence (e₁.trans e₂) := by
  cases 𝒞₁
  dsimp [ofEquivalence]
  congr <;> simp [Equivalence.counitInv]

/--
Don't use this lemma, ever. instead go via Classifier.uniqueUpToIso .
It exists to verify that this construction will have nice defeq properties.
See also Classifier.ofEquivalence_trans
-/
lemma Classifier.ofEquivalence_refl (𝒞₁ : Classifier C) :
    𝒞₁.ofEquivalence (.refl) = 𝒞₁ := by
  cases 𝒞₁
  dsimp [ofEquivalence]
  congr <;> simp [Equivalence.counitInv]

@[simps]
def Classifier.ofIso (𝒞 : Classifier C) {Ω₀ Ω : C} (eΩ : 𝒞.Ω ≅ Ω) (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀)
    (bang : ∀ C, C ⟶ Ω₀) {t : Ω₀ ⟶ Ω} (ht : t = eΩ₀.inv ≫ 𝒞.truth ≫ eΩ.hom) :
    Classifier C where
  Ω₀ := Ω₀
  Ω := Ω
  truth := t
  mono_truth := ht ▸ inferInstance
  χ₀ := bang
  χ {F G} m _ := (𝒞.χ m) ≫ eΩ.hom
  isPullback {F G} m _ := by
    rw [eΩ₀.comp_inv_eq.mp (Subsingleton.elim (bang F ≫ eΩ₀.inv) (𝒞.χ₀ F))]
    exact (𝒞.isPullback m).paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
  uniq {F G} m _ := by
    intro χ₀' χ' hχ'
    have : χ' ≫ eΩ.inv = 𝒞.χ m := by
      apply 𝒞.uniq m (χ₀' := χ₀' ≫ eΩ₀.inv)
      exact hχ'.paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
    simpa using congr($this ≫ eΩ.hom)

alias Classifier.copy := Classifier.ofIso

end CategoryTheory
