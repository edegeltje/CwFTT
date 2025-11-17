
import CwFTT.Classifier.Ops

universe v u
namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]

structure LTT (𝒞 : Classifier C) [HasFiniteLimits C] where
  locally : 𝒞.Ω ⟶ 𝒞.Ω
  locally_true : 𝒞.truth ≫ locally = 𝒞.truth
  locally_locally : locally ≫ locally = locally
  locally_and : 𝒞.and ≫ locally = prod.map locally locally ≫ 𝒞.and

attribute [reassoc] LTT.locally_true LTT.locally_locally LTT.locally_and

def LTT.χclosure {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : Y ⟶ 𝒞.Ω := 𝒞.χ m ≫ j.locally

noncomputable def LTT.closureObj {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : C := pullback (j.χclosure m) 𝒞.truth
noncomputable def LTT.closure {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : j.closureObj m ⟶ Y := pullback.fst (j.χclosure m) 𝒞.truth

instance {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : Mono (j.closure m) :=
  IsPullback.mono_fst (.of_hasPullback (j.χclosure m) 𝒞.truth)

lemma LTT.closure_isPullback {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] :
    IsPullback (j.closure m) (𝒞.χ₀ _) (j.χclosure m) (𝒞.truth) := by
  convert IsPullback.of_hasPullback (j.χclosure m) (𝒞.truth)
  apply Subsingleton.elim

@[simp]
lemma LTT.χ_closure_eq {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : 𝒞.χ (j.closure m) = j.χclosure m := by
  dsimp [closure,LTT.χclosure]
  symm
  exact 𝒞.uniq _ <| j.closure_isPullback m

noncomputable def LTT.closureEmbed {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : X ⟶ j.closureObj m := pullback.lift m (𝒞.χ₀ _)
    (by
      dsimp [LTT.χclosure]
      rw [(𝒞.isPullback m).w_assoc, j.locally_true])


--@[reassoc] -- not sure if this should be simp, tbh
lemma LTT.closureEmbed_closure_eq {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] :
  j.closureEmbed m ≫ j.closure m = m := pullback.lift_fst _ _ _

instance {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : Mono (j.closureEmbed m) :=
  mono_of_mono_fac (j.closureEmbed_closure_eq m)

/--
A monomorphism `m : X ⟶ Y` is `j`-dense when the closure of the subobject it represents is
the entire subobject. Intuitively, it says that the property determining the subobject
`X` is a (`j`-)local one -/
@[mk_iff]
class LTT.IsDense {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : Prop where
  χ_locally_eq_χ_id : 𝒞.χ m ≫ j.locally = 𝒞.χ (𝟙 _)

attribute [reassoc] LTT.IsDense.χ_locally_eq_χ_id

-- there can be an iff-lemma for this
lemma LTT.IsDense.isPullback {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} {m : X ⟶ Y} [Mono m] (hm : j.IsDense m) :
    IsPullback (𝟙 Y) (𝒞.χ₀ Y) (𝒞.χ m ≫ j.locally) (𝒞.truth) := by
  convert 𝒞.isPullback (𝟙 Y)
  exact hm.χ_locally_eq_χ_id

@[mk_iff]
structure LTT.IsClosed {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : Prop where
  χ_locally_eq_χ_self : 𝒞.χ m ≫ j.locally = 𝒞.χ m

attribute [reassoc] LTT.IsClosed.χ_locally_eq_χ_self

-- there can be an iff-lemma for this
lemma LTT.IsClosed.isPullback {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} {m : X ⟶ Y} [Mono m] (hm : j.IsClosed m) :
    IsPullback m (𝒞.χ₀ X) (𝒞.χ m ≫ j.locally) (𝒞.truth) := by
  convert 𝒞.isPullback m
  exact hm.χ_locally_eq_χ_self

-- there can be an iff-lemma for this

lemma LTT.closure_isClosed {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} (m : X ⟶ Y) [Mono m] : j.IsClosed (j.closure m) := by
  rw [j.isClosed_iff, j.χ_closure_eq,LTT.χclosure,Category.assoc,j.locally_locally]

lemma LTT.χclosure_eq_χ_id_of_isDense {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} {m : X ⟶ Y} [Mono m] (hm : j.IsDense m) : j.χclosure m = 𝒞.χ (𝟙 _) :=
  hm.χ_locally_eq_χ_id

-- not sure this is terribly useful, but still a fun fact.
lemma LTT.χclosure_isDense_of_isDense {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} {m : X ⟶ Y} [Mono m] (hm : j.IsDense m) : j.IsDense (j.closure m) where
  χ_locally_eq_χ_id := by
    simp only [χ_closure_eq, j.χclosure_eq_χ_id_of_isDense hm]
    rw [Classifier.χ_id_assoc,Classifier.χ_id,j.locally_true]

/-- The intersection of two dense subobjects is again dense. -/
lemma LTT.IsDense.of_isPullback {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X₁ X₂ X₃ X₄ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄}
    [Mono f₃] [Mono f₄] (hf : IsPullback f₁ f₂ f₃ f₄) (hf₃ : j.IsDense f₃) (hf₄ : j.IsDense f₄) :
    letI : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
    j.IsDense (f₁ ≫ f₃) := by
  rw [j.isDense_iff,𝒞.χ_pullback hf,Category.assoc,j.locally_and, prod.lift_map_assoc,
    hf₃.χ_locally_eq_χ_id, hf₄.χ_locally_eq_χ_id,← 𝒞.χ_pullback (.id_vert (𝟙 _))]
  simp

/-- The intersection of two closed subobjects is again closed. -/
lemma LTT.IsClosed.of_isPullback {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X₁ X₂ X₃ X₄ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄}
    [Mono f₃] [Mono f₄] (hf : IsPullback f₁ f₂ f₃ f₄) (hf₃ : j.IsClosed f₃) (hf₄ : j.IsClosed f₄) :
    letI : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
    j.IsClosed (f₁ ≫ f₃) := by
  rw [j.isClosed_iff,𝒞.χ_pullback hf,Category.assoc,j.locally_and, prod.lift_map_assoc,
    hf₃.χ_locally_eq_χ_self, hf₄.χ_locally_eq_χ_self]

lemma LTT.IsDense.closure_isIso {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} {m : X ⟶ Y} [Mono m] (hm : j.IsDense m) : IsIso (j.closure m) := by
  have h : 𝟙 Y ≫ j.χclosure m = 𝒞.χ₀ Y ≫ 𝒞.truth := by
    rw [j.χclosure_eq_χ_id_of_isDense hm]
    exact (𝒞.isPullback (𝟙 Y)).w
  constructor
  use (j.closure_isPullback m).lift (𝟙 Y) (𝒞.χ₀ _) h
  constructor
  · apply (j.closure_isPullback m).hom_ext
    · rw [Category.assoc,(j.closure_isPullback m).lift_fst]
      simp
    · rw [Category.assoc,(j.closure_isPullback m).lift_snd]
      simp
  · exact (j.closure_isPullback m).lift_fst (𝟙 Y) (𝒞.χ₀ Y) h

lemma LTT.IsClosed.of_isClosed_comp_right {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y Z : C} {m₁ : X ⟶ Y} {m₂ : Y ⟶ Z} [Mono m₁] [Mono m₂] (hm : j.IsClosed (m₁ ≫ m₂)) :
    j.IsClosed m₁ := by
  rw [j.isClosed_iff] at hm ⊢
  rw [← 𝒞.comp_χ_comp m₁ m₂,Category.assoc,hm]


lemma LTT.IsDense.of_isDense_comp_right {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y Z : C} {m₁ : X ⟶ Y} {m₂ : Y ⟶ Z} [Mono m₁] [Mono m₂] (hm : j.IsDense (m₁ ≫ m₂)) :
    j.IsDense m₁ := by
  rw [j.isDense_iff] at hm ⊢
  rw [← 𝒞.comp_χ_comp m₁ m₂, Category.assoc, hm, 𝒞.χ_id, 𝒞.χ_id,
    reassoc_of% Subsingleton.elim (m₂ ≫ 𝒞.χ₀ _) (𝒞.χ₀ _)]

/-- there is a unique map from -/
noncomputable def LTT.closureLift {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y Z : C} (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] (hg : j.IsClosed g) :
    j.closureObj (f ≫ g) ⟶ Y := by
  dsimp [LTT.closureObj]
  have := hg.isPullback
  apply hg.isPullback.lift (j.closure (f ≫ g)) (𝒞.χ₀ _) _

  trans 𝒞.χ (pullback.fst (j.closure (f ≫ g) ≫ 𝒞.χ g ≫ j.locally) (𝒞.truth))
  · apply 𝒞.uniq
    exact IsPullback.of_hasPullback _ _
  · sorry
  -- pullback.lift (j.closure _) (𝒞.χ₀ _) (by
  --   suffices h : j.closure (f ≫ j.closureEmbed g ≫ j.closure g) ≫ j.χclosure g =
  --     𝒞.χ₀ (j.closureObj (f ≫ j.closureEmbed g ≫ j.closure g)) ≫ 𝒞.truth by
  --     convert h
  --     all_goals exact (j.closureEmbed_closure_eq g).symm

  --   sorry
  --   )

-- if m₁ is j-dense, then j.closure is an iso.

-- if m₁ ≫ m₂ is j-dense, then 𝒞.χ (m₁ ≫ m₂) ≫ j.locally factors through 𝒞.truth
-- this map is given by `j.closure m₁ ≫ j.closureEmbed m₂`, such that
-- `j.closure m₁ ≫ j.closureEmbed m₂ ≫ j.closure m₂ = j.closure m₁ ≫ m₂`

-- lemma LTT.IsDense.of_isDense_comp_left {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
--     {X Y Z : C} {m₁ : X ⟶ Y} {m₂ : Y ⟶ Z} [Mono m₁] [Mono m₂] (hm : j.IsDense (m₁ ≫ m₂)) :
--     j.IsDense m₂ := by
--   rw [j.isDense_iff] at ⊢
--   have := hm.closure_isIso
--   apply 𝒞.uniq
--   change IsPullback (𝟙 X) (j.closureEmbed m₁ ≫ j.closure m₁ ≫ j.closureEmbed m₂ ≫
--     j.closure m₂ ≫ 𝒞.χ₀ _) (j.χclosure m₂) _
--   rw [← Category.id_comp (j.χclosure m₂)]
--   refine IsPullback.paste_vert ?_ (j.closure_isPullback m₂)
--   sorry
  --rw [← j.χclosure]
  -- rw [← Category.id_comp (j.locally)]
  -- refine IsPullback.paste_vert

  -- rw [← 𝒞.comp_χ_comp m₁ m₂, Category.assoc, hm, 𝒞.χ_id, 𝒞.χ_id,
  --   reassoc_of% Subsingleton.elim (m₂ ≫ 𝒞.χ₀ _) (𝒞.χ₀ _)]


noncomputable def LTT.IsDense.isoSelf {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y : C} {m : X ⟶ Y} [Mono m] (hm₁ : j.IsDense m) :
    Y ≅ j.closureObj m :=
  IsPullback.isoPullback (fst := 𝟙 _) (snd := 𝒞.χ₀ _) (by
    convert 𝒞.isPullback (𝟙 Y) using 1
    exact j.χclosure_eq_χ_id_of_isDense hm₁)


-- lemma LTT.IsDense.ofIso {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
--     {X Y : C} {m : X ⟶ Y} [Mono m] (hm₁ : j.IsDense m) :


/-

given {X Y Z : C} {m₁ : X ⟶ Y} {m₂ : Y ⟶ Z}, `j.closure m₁ ≫ m₂` is a subobject of Z.
Additionally, it is j.closed (.? , if m₂ is.?).
-/
-- something something "the closure of m₁ ≫ m₂ factors through the closure of m₁"
-- as a result, the closure of m₁ in m₂ must be contained in the closure of


-- if (`closure_Y X ≅ Y`) and (closure_Z Y ≅ Z), then (closure_Z X ≅ Z))?
-- somehow i'd like that 𝒞.χ m₂ factors through m₁, somehow
-- lemma LTT.IsClosed.of_comp {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
--     {X Y Z : C} {m₁ : X ⟶ Y} {m₂ : Y ⟶ Z} [Mono m₁] [Mono m₂]
--     (hm₁ : j.IsClosed m₁) (hm₂ : j.IsClosed m₂) : j.IsClosed (m₁ ≫ m₂) := by
--   simp [j.isClosed_iff] at hm₁ hm₂ ⊢
--   rw [← 𝒞.comp_χ_comp_assoc m₁ m₂] at hm₁
--   sorry

-- #check 𝒞.comp_χ_comp
-- if m₁ ≫ m₂ is dense, then j.χclosure (m₁ ≫ m₂) = 𝒞.χ (id), so then
--
-- intuition says this is true, but i'm not sure
lemma LTT.IsDense.of_isDense_comp_left {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞)
    {X Y Z : C} {m₁ : X ⟶ Y} {m₂ : Y ⟶ Z} [Mono m₁] [Mono m₂] (hm : j.IsDense (m₁ ≫ m₂)) :
    j.IsDense m₂ := by
  rw [j.isDense_iff] at hm ⊢
  sorry
  -- rw [← hm, 𝒞.χ_id, 𝒞.χ_id,
  --   reassoc_of% Subsingleton.elim (m₂ ≫ 𝒞.χ₀ _) (𝒞.χ₀ _)]


/--
An object `X` is `j`-separated if for every
-/
@[mk_iff]
structure LTT.IsSeparated {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞) (X : C) : Prop where
  diag_closed : j.IsClosed (diag X)
  -- if the diagonal map is closed, then `χ (diag X) ≫ locally = χ (diag X)`.
  -- this means that for (f g : Y ⟶ X) and (m : U ⟶ Y) dense, if
  -- `m ≫ f = m ≫ g`, then f = g.

lemma LTT.isSeparated_iff_ {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞) (F : C) :
  j.IsSeparated F ↔ ∀ {A B : C}, ∀ (f g : B ⟶ F), ∀ (m : A ⟶ B) [Mono m],
    j.IsDense m → m ≫ f = m ≫ g → f = g := by
  constructor
  · intro h U Y f g m inst hm heq
    have := (equalizer.lift_ι m heq).symm
    generalize inst = inst'
    revert inst hm
    rw [this]
    clear this
    intro _ hm
    have : Mono (equalizer.lift m heq) := mono_of_mono_fac (equalizer.lift_ι m heq)
    have : j.IsDense (equalizer.lift m heq) :=
      .of_isDense_comp_right _ hm
    rw [j.isSeparated_iff,j.isClosed_iff] at h



    sorry
  sorry


/--
An object `X` is a `j`-sheaf if for every `j`-dense morphism `m : R ⟶ Y`,
the induced map (Y ⟶ X) → (R ⟶ X) is a bijection
-/
structure LTT.IsSheaf {𝒞 : Classifier C} [HasFiniteLimits C] (j : LTT 𝒞) (X : C) : Prop where
  of_bijective {R Y : C} (m : R ⟶ Y) [Mono m] (hm : j.IsDense m) :
    Function.Bijective (m ≫ · : _ → (R ⟶ X))


-- independent of the classifier, we get a LTT.



end CategoryTheory
