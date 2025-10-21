import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monad.Adjunction
import CwFTT.Util.Pullback

namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

/- these lemmas should really be in Topos.Classifier or something -/
section

instance (𝒞 : Classifier C) (X : C) : HasBinaryProduct 𝒞.Ω₀ X where
  exists_limit := ⟨⟨BinaryFan.mk (𝒞.χ₀ X) (𝟙 X),by
    apply Classical.choice
    rw [BinaryFan.isLimit_iff_isIso_snd (𝒞.isTerminalΩ₀)]
    simpa using IsIso.id X
    ⟩
  ⟩

@[reassoc]
lemma Classifier.χ_id (𝒞 : Classifier C) (X : C) : 𝒞.χ (𝟙 X) = 𝒞.χ₀ _ ≫ 𝒞.truth :=
  (𝒞.uniq _ (χ₀' := 𝒞.χ₀ _) <| IsPullback.of_horiz_isIso_mono (by simp)).symm

@[reassoc]
lemma Classifier.comp_χ_comp (𝒞 : Classifier C) {X Y Z : C}
    (m₁ : X ⟶ Y) [Mono m₁] (m₂ : Y ⟶ Z) [Mono m₂] :
    m₂ ≫ 𝒞.χ (m₁ ≫ m₂) = 𝒞.χ m₁ := 𝒞.uniq _ (χ₀' := 𝟙 X ≫ _) <|
  .paste_vert (.of_vert_isIso_mono (by simp)) (𝒞.isPullback (m₁ ≫ m₂))

-- @[ext (iff := false)]
lemma Classifier.hom_ext (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) {Y : C} {m : Y ⟶ X}
    (χ₀ : Y ⟶ 𝒞.Ω₀) (χ₀' : Y ⟶ 𝒞.Ω₀)
    (hf : IsPullback m χ₀ f 𝒞.truth) (hg : IsPullback m χ₀' g 𝒞.truth) :
    f = g := by
  letI : Mono m := hf.mono_fst
  trans 𝒞.χ m
  · exact 𝒞.uniq _ hf
  · symm
    exact 𝒞.uniq _ hg

-- lemma Classifier.hom_ext_iff (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) (m : ) :
--     f = g ↔ IsPullback (pullback.fst g 𝒞.truth) (𝒞.χ₀ _) f 𝒞.truth := by
--   refine ⟨?_,𝒞.hom_ext f g _⟩
--   intro heq
--   convert IsPullback.of_hasPullback g 𝒞.truth
--   exact Subsingleton.elim _ _

@[reassoc (attr := simp)]
lemma Classifier.comp_χ₀ (𝒞 : Classifier C) {X Y : C} (m : X ⟶ Y) :
  m ≫ 𝒞.χ₀ _ = 𝒞.χ₀ _ := Subsingleton.elim _ _

lemma Classifier.χ_pullback_fst (𝒞 : Classifier C) {X : C} (a : X ⟶ 𝒞.Ω) [HasPullback a 𝒞.truth] :
  𝒞.χ (pullback.fst a 𝒞.truth) = a := by
  symm
  apply 𝒞.uniq
  exact .of_hasPullback _ _

end
section and
noncomputable abbrev Classifier.and (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] :
    𝒞.Ω ⨯ 𝒞.Ω ⟶ 𝒞.Ω :=
  𝒞.χ (Limits.prod.map 𝒞.truth 𝒞.truth)

lemma Classifier.and_isPullback (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] :
    IsPullback (prod.map 𝒞.truth 𝒞.truth) (𝒞.χ₀ _) (𝒞.and) (𝒞.truth) := 𝒞.isPullback _

lemma Classifier.χ_pullback [HasBinaryProducts C] {𝒞 : Classifier C} {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} [Mono f₃] {f₄ : X₃ ⟶ X₄} [Mono f₄]
    (hf : IsPullback f₁ f₂ f₃ f₄) :
    letI : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
    𝒞.χ (f₁ ≫ f₃) = Limits.prod.lift (𝒞.χ f₃) (𝒞.χ f₄) ≫ 𝒞.and := by
  symm
  have : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
  refine 𝒞.uniq _ (χ₀' := 𝒞.χ₀ _) ?_
  rw [Classifier.truth]
  convert IsPullback.paste_vert (IsPullback.pullback_fst (𝒞.isPullback f₃) (𝒞.isPullback f₄) hf)
    (𝒞.isPullback (Limits.prod.map 𝒞.truth 𝒞.truth))

  apply Subsingleton.elim

lemma Classifier.and_comm_aux (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] :
    (prod.braiding _ _).hom ≫ 𝒞.and = 𝒞.and := by
  dsimp [Classifier.and]
  apply 𝒞.uniq _ (χ₀' := (prod.braiding _ _).hom ≫ 𝒞.χ₀ _)
  have : IsPullback (prod.map 𝒞.truth 𝒞.truth)
      (prod.braiding _ _).hom (prod.braiding _ _).hom (prod.map 𝒞.truth 𝒞.truth) := by
    exact .of_vert_isIso_mono (by simp)
  exact (this).paste_vert (𝒞.isPullback (prod.map 𝒞.truth 𝒞.truth))

lemma Classifier.and_comm (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] {X : C} (f g : X ⟶ 𝒞.Ω) :
    prod.lift f g ≫ 𝒞.and = prod.lift g f ≫ 𝒞.and := by
  nth_rw 1 [← 𝒞.and_comm_aux]
  simp only [prod.braiding_hom, ← Category.assoc]
  congr
  ext <;> simp

lemma Classifier.and_assoc_aux (𝒞 : Classifier C) [HasBinaryProducts C] :
    (prod.associator ..).hom ≫ prod.map (𝟙 _) (𝒞.and) ≫ 𝒞.and = prod.map (𝒞.and) (𝟙 _) ≫ 𝒞.and := by
  apply 𝒞.hom_ext _ _ (m := prod.map (prod.map (𝒞.truth) 𝒞.truth) (𝒞.truth))
  · have assoc : IsPullback (prod.map (prod.map 𝒞.truth 𝒞.truth) 𝒞.truth)
        (prod.associator _ _ _).hom (prod.associator _ _ _).hom
        (prod.map 𝒞.truth (prod.map 𝒞.truth 𝒞.truth)) := by
      exact .of_vert_isIso_mono (by simp)
    have := ((IsPullback.id_vert 𝒞.truth).prod 𝒞.and_isPullback).paste_vert 𝒞.and_isPullback
    exact assoc.paste_vert this
  · exact (𝒞.and_isPullback.prod (IsPullback.id_vert 𝒞.truth)).paste_vert 𝒞.and_isPullback

lemma Classifier.and_assoc (𝒞 : Classifier C) [HasBinaryProducts C] {X : C} (f g h : X ⟶ 𝒞.Ω) :
    prod.lift (prod.lift f g ≫ 𝒞.and) h ≫ 𝒞.and = prod.lift f (prod.lift g h ≫ 𝒞.and) ≫ 𝒞.and := by
  trans prod.lift (prod.lift f g) h ≫ prod.map 𝒞.and (𝟙 _) ≫ 𝒞.and
  · simp
  · rw [← 𝒞.and_assoc_aux]
    simp [← Category.assoc]
end and

section colimits
open scoped MonoidalCategory CartesianMonoidalCategory

/--
naturality is shown by uncurrying, and showing that the following diagram commutes:
https://q.uiver.app/#q=WzAsMTksWzEsMCwiWCJdLFsxLDEsIlxcT21lZ2Fee1xcT21lZ2FeWH0iXSxbMiwwLCJYXFx0aW1lcyBcXE9tZWdhXlgiXSxbMiwxLCJcXE9tZWdhXntcXE9tZWdhXlh9XFx0aW1lcyBcXE9tZWdhXlgiXSxbMywxLCJcXE9tZWdhIl0sWzMsMCwiXFxPbWVnYV5YXFx0aW1lcyBYIl0sWzAsMiwiXFxPbWVnYV57XFxPbWVnYV5ZfSJdLFswLDEsIlkiXSxbMCw0LCJcXE9tZWdhXntcXE9tZWdhXlh9XFx0aW1lcyBcXE9tZWdhXlkiXSxbMCw1LCJcXE9tZWdhXntcXE9tZWdhXll9XFx0aW1lcyBcXE9tZWdhXlkiXSxbMiw2LCJcXE9tZWdhIl0sWzEsNCwiXFxPbWVnYV57XFxPbWVnYV5YfVxcdGltZXMgXFxPbWVnYV5YIl0sWzIsMiwiWFxcdGltZXNcXE9tZWdhXlkiXSxbMSwzLCJYXFx0aW1lc1xcT21lZ2FeWCJdLFsyLDQsIlxcT21lZ2FeWFxcdGltZXMgWCJdLFszLDMsIlxcT21lZ2FeWVxcdGltZXMgWCJdLFszLDQsIlxcT21lZ2FeWVxcdGltZXMgWSJdLFs0LDQsIllcXHRpbWVzXFxPbWVnYV5ZIl0sWzQsNSwiXFxPbWVnYV57XFxPbWVnYV5ZfVxcdGltZXMgXFxPbWVnYV5ZIl0sWzMsNCwiZXYiXSxbMCwxLCJcXGxhbWJkYV97XFxiZXRhXFxnZyBldn0iLDFdLFsyLDMsIlxcbGFtYmRhX3tcXGJldGFcXGdnIGV2fVxcdGltZXMgaWRfe1xcT21lZ2FeWH0iLDFdLFsyLDUsIlxcYmV0YSIsMl0sWzUsNCwiZXYiLDJdLFsxLDYsIlxcT21lZ2Fee1xcT21lZ2FeZn0iXSxbMCw3LCJmIiwyXSxbNyw2LCJcXGxhbWJkYV97XFxiZXRhXFxnZyBldn0iLDJdLFs5LDEwLCJldiIsMl0sWzgsOSwiXFxPbWVnYV57XFxPbWVnYV5mfVxcdGltZXMgaWQiXSxbOCwxMSwiaWRcXHRpbWVzIFxcT21lZ2FeZiJdLFsxMSwxMCwiZXYiXSxbMTIsOCwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lcyBpZCIsMix7ImN1cnZlIjoyfV0sWzEyLDEzLCJpZFxcdGltZXNcXE9tZWdhXmYiLDFdLFsxMywxMSwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lcyBpZCIsMV0sWzEzLDE0LCJcXGJldGEiLDFdLFsxNCwxMCwiZXYiXSxbMTIsMTUsIlxcYmV0YSIsMV0sWzE1LDE0LCJcXE9tZWdhXmZcXHRpbWVzIGlkIiwxXSxbMTYsMTAsImV2Il0sWzE1LDE2LCJpZFxcdGltZXMgZiIsMV0sWzEyLDE3LCJmXFx0aW1lcyBpZCIsMSx7ImN1cnZlIjotMn1dLFsxNywxNiwiXFxiZXRhIiwxXSxbMTcsMTgsIlxcbGFtYmRhX3tcXGJldGFcXGdnIGV2fVxcdGltZXMgaWQiLDFdLFsxOCwxMCwiZXYiLDFdXQ==
-/
def CartesianClosed.internalHom.unit [CartesianMonoidalCategory C] [BraidedCategory C] [CartesianClosed C] (X : C) :
  𝟭 C ⟶ (internalHom.flip.obj X ⋙ opOp C).unop ⋙ (internalHom.flip.obj X) where
    app Y :=
      CartesianClosed.curry <| (β_ _ Y).hom ≫ ((exp.ev _).app _)
    naturality {Y₁ Y₂} f := by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.unop_obj, Functor.flip_obj_obj, opOp_obj,
        Functor.id_map, Functor.comp_map, Functor.unop_map, Functor.flip_obj_map, opOp_map,
        Quiver.Hom.unop_op]
      apply CartesianClosed.uncurry_injective
      calc uncurry (f ≫ curry ((β_ ((internalHom.obj (Opposite.op Y₂)).obj X) Y₂).hom ≫
          (exp.ev Y₂).app X))
      _ = _ ◁ f ≫ uncurry (curry ((β_ ((internalHom.obj (Opposite.op Y₂)).obj X) Y₂).hom ≫
          (exp.ev Y₂).app X)) := by
        rw [CartesianClosed.uncurry_natural_left]
      _ = _ ◁ f ≫ ((β_ ((internalHom.obj (Opposite.op Y₂)).obj X) _).hom ≫
          (exp.ev Y₂).app X) := by rw [CartesianClosed.uncurry_curry]
      _ = (β_ ((internalHom.obj (Opposite.op Y₂)).obj X) _).hom ≫ f ▷ _ ≫ (exp.ev Y₂).app X := by
        simp
      _ = (β_ ((internalHom.obj (Opposite.op Y₂)).obj X) Y₁).hom ≫
          Y₁ ◁ (internalHom.map f.op).app X ≫ (exp.ev Y₁).app X := by
        congr 1
        dsimp [internalHom,pre]
        sorry
      _ = uncurry (curry ((β_ ((internalHom.obj (Opposite.op Y₁)).obj X) Y₁).hom ≫
        (exp.ev Y₁).app X) ≫ (internalHom.map ((internalHom.map f.op).app X).op).app X) := by
        sorry

variable [HasFiniteLimits C]


/-- the contravariant functor mapping objects `X` to "the object representing its subobjects",
  which is `X ⟹ 𝒞.Ω` -/
@[simps!]
def Classifier.P (𝒞 : Classifier C) [HasFiniteLimits C]
  [CartesianMonoidalCategory C] [CartesianClosed C] :
    Cᵒᵖ ⥤ C := internalHom.flip.obj 𝒞.Ω

@[simps!]
def Classifier.POp (𝒞 : Classifier C) [HasFiniteLimits C]
    [CartesianMonoidalCategory C] [CartesianClosed C] : C ⥤ Cᵒᵖ :=
  (𝒞.P ⋙ opOp C).unop

def Classifier.P_unit (𝒞 : Classifier C) [HasFiniteLimits C]
    [CartesianMonoidalCategory C] [CartesianClosed C] : 𝟭 C ⟶ 𝒞.POp ⋙ 𝒞.P where
  app X :=
    letI : BraidedCategory C := .ofCartesianMonoidalCategory
    CartesianClosed.curry <| (β_ _ X).hom ≫ (exp.ev X).app 𝒞.Ω
  naturality {X Y} f := sorry

def Classifier.P_adjoint (𝒞 : Classifier C) [HasFiniteLimits C]
    [CartesianMonoidalCategory C] [CartesianClosed C] :
    𝒞.POp ⊣ 𝒞.P where
  unit := 𝒞.P_unit
  --   letI : BraidedCategory C := _
  -- unit.naturality {X Y} f := by
  --   apply CartesianClosed.uncurry_injective
  --   simp_rw [CartesianClosed.uncurry_natural_left,CartesianClosed.uncurry_curry]


  --   sorry
  counit := sorry
  left_triangle_components := sorry
  right_triangle_components := sorry

instance (𝒞 : Classifier C) [HasFiniteLimits C] [CartesianMonoidalCategory C] [CartesianClosed C] :
    MonadicRightAdjoint (𝒞.P) where
  L := 𝒞.POp
  adj := 𝒞.P_adjoint
  eqv := sorry

end colimits



-- don't worry about this for now
noncomputable abbrev Classifier.«→» (𝒞 : Classifier C) [HasFiniteLimits C]
    [HasEqualizer 𝒞.and Limits.prod.fst] : 𝒞.Ω ⨯ 𝒞.Ω ⟶ 𝒞.Ω :=
  𝒞.χ (Limits.equalizer.ι 𝒞.and Limits.prod.fst)



end CategoryTheory
