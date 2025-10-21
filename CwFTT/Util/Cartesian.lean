import Mathlib.CategoryTheory.Closed.Cartesian
universe v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [CartesianClosed C]
open Limits MonoidalCategory CartesianMonoidalCategory

-- @[simp]
lemma internalHom.obj_obj (X Y : C) :
  (internalHom.obj (.op X)).obj Y = (exp X).obj Y := rfl

-- @[simp]
lemma internalHom.obj_map (X Y Z : C) (f : Y ⟶ Z) :
  (internalHom.obj (.op X)).map f = (exp X).map f := rfl

-- @[simp]
lemma uncurry_internalHom_map_app (X Y Z : C) (f : Y ⟶ Z) :
    CartesianClosed.uncurry ((internalHom.map f.op).app X) = f ▷ (internalHom.obj _).obj _ ≫
      (exp.ev _).app X := by
  exact uncurry_pre _ _

-- there is a one-line proof which (ab)uses defeq, but this seems better.
-- @[simp]
lemma internalHom.map_app_eq (X Y Z : C) (f : Y ⟶ Z) :
    (internalHom.map f.op).app X = CartesianClosed.curry (f ▷ (internalHom.obj _).obj _ ≫
      (exp.ev _).app X) := by
  apply CartesianClosed.uncurry_injective
  rw [CartesianClosed.uncurry_curry,uncurry_internalHom_map_app]

/--
naturality is shown by uncurrying, then showing that the following diagram commutes:
https://q.uiver.app/#q=WzAsMTksWzEsMCwiWCJdLFsxLDEsIlxcT21lZ2Fee1xcT21lZ2FeWH0iXSxbMiwwLCJYXFx0aW1lcyBcXE9tZWdhXlgiXSxbMiwxLCJcXE9tZWdhXntcXE9tZWdhXlh9XFx0aW1lcyBcXE9tZWdhXlgiXSxbMywxLCJcXE9tZWdhIl0sWzMsMCwiXFxPbWVnYV5YXFx0aW1lcyBYIl0sWzAsMiwiXFxPbWVnYV57XFxPbWVnYV5ZfSJdLFswLDEsIlkiXSxbMCw0LCJcXE9tZWdhXntcXE9tZWdhXlh9XFx0aW1lcyBcXE9tZWdhXlkiXSxbMCw1LCJcXE9tZWdhXntcXE9tZWdhXll9XFx0aW1lcyBcXE9tZWdhXlkiXSxbMiw2LCJcXE9tZWdhIl0sWzEsNCwiXFxPbWVnYV57XFxPbWVnYV5YfVxcdGltZXMgXFxPbWVnYV5YIl0sWzIsMiwiWFxcdGltZXNcXE9tZWdhXlkiXSxbMSwzLCJYXFx0aW1lc1xcT21lZ2FeWCJdLFsyLDQsIlxcT21lZ2FeWFxcdGltZXMgWCJdLFszLDMsIlxcT21lZ2FeWVxcdGltZXMgWCJdLFszLDQsIlxcT21lZ2FeWVxcdGltZXMgWSJdLFs0LDQsIllcXHRpbWVzXFxPbWVnYV5ZIl0sWzQsNSwiXFxPbWVnYV57XFxPbWVnYV5ZfVxcdGltZXMgXFxPbWVnYV5ZIl0sWzMsNCwiZXYiXSxbMCwxLCJcXGxhbWJkYV97XFxiZXRhXFxnZyBldn0iLDFdLFsyLDMsIlxcbGFtYmRhX3tcXGJldGFcXGdnIGV2fVxcdGltZXMgaWRfe1xcT21lZ2FeWH0iLDFdLFsyLDUsIlxcYmV0YSIsMl0sWzUsNCwiZXYiLDJdLFsxLDYsIlxcT21lZ2Fee1xcT21lZ2FeZn0iXSxbMCw3LCJmIiwyXSxbNyw2LCJcXGxhbWJkYV97XFxiZXRhXFxnZyBldn0iLDJdLFs5LDEwLCJldiIsMl0sWzgsOSwiXFxPbWVnYV57XFxPbWVnYV5mfVxcdGltZXMgaWQiXSxbOCwxMSwiaWRcXHRpbWVzIFxcT21lZ2FeZiJdLFsxMSwxMCwiZXYiXSxbMTIsOCwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lcyBpZCIsMix7ImN1cnZlIjoyfV0sWzEyLDEzLCJpZFxcdGltZXNcXE9tZWdhXmYiLDFdLFsxMywxMSwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lcyBpZCIsMV0sWzEzLDE0LCJcXGJldGEiLDFdLFsxNCwxMCwiZXYiXSxbMTIsMTUsIlxcYmV0YSIsMV0sWzE1LDE0LCJcXE9tZWdhXmZcXHRpbWVzIGlkIiwxXSxbMTYsMTAsImV2Il0sWzE1LDE2LCJpZFxcdGltZXMgZiIsMV0sWzEyLDE3LCJmXFx0aW1lcyBpZCIsMSx7ImN1cnZlIjotMn1dLFsxNywxNiwiXFxiZXRhIiwxXSxbMTcsMTgsIlxcbGFtYmRhX3tcXGJldGFcXGdnIGV2fVxcdGltZXMgaWQiLDFdLFsxOCwxMCwiZXYiLDFdXQ==
-/
@[simps]
def CartesianClosed.internalHom.unit [CartesianMonoidalCategory C] [BraidedCategory C]
    [CartesianClosed C] (X : C) :
  𝟭 C ⟶ (internalHom.flip.obj X ⋙ opOp C).unop ⋙ (internalHom.flip.obj X) where
    app Y :=
      CartesianClosed.curry <| (β_ _ Y).hom ≫ ((exp.ev _).app _)
    naturality {Y₁ Y₂} f := by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.unop_obj, Functor.flip_obj_obj, opOp_obj,
        Functor.id_map, Functor.comp_map, Functor.unop_map, Functor.flip_obj_map, opOp_map,
        Quiver.Hom.unop_op]
      apply CartesianClosed.uncurry_injective
      rw [CartesianClosed.uncurry_natural_left, uncurry_curry,
        BraidedCategory.braiding_naturality_right_assoc, ← uncurry_internalHom_map_app, uncurry_eq,
        ← BraidedCategory.braiding_naturality_left_assoc ((internalHom.map f.op).app X),
        uncurry_natural_left, uncurry_internalHom_map_app, MonoidalCategory.whisker_exchange_assoc,
        ← uncurry_eq, uncurry_curry]

@[simps]
def CartesianClosed.internalHom.counit [CartesianMonoidalCategory C] [BraidedCategory C]
    [CartesianClosed C] (X : C) :
  (internalHom.flip.obj X) ⋙ (internalHom.flip.obj X ⋙ opOp C).unop ⟶ 𝟭 Cᵒᵖ where
    app Z := ((internalHom.unit X).app (Z.unop)).op
    naturality {Y₁ Y₂} f := by
      rw [Functor.comp_map,Functor.unop_map,Functor.comp_map]
      rw [opOp_map]
      simp only [Functor.id_obj, Functor.flip_obj_map, Quiver.Hom.unop_op, Functor.id_map]
      exact congr($((internalHom.unit X).naturality f.unop).op).symm

/--
the proof is by showing the following diagram commutes:
https://q.uiver.app/#q=WzAsMjAsWzEsMCwiWCJdLFsxLDEsIlxcT21lZ2Fee1xcT21lZ2FeWH0iXSxbMiwxLCJcXE9tZWdhXntcXE9tZWdhXlh9XFx0aW1lcyBcXE9tZWdhXlgiXSxbMywxLCJcXE9tZWdhIl0sWzMsMCwiXFxPbWVnYV5YXFx0aW1lcyBYIl0sWzAsMiwiXFxPbWVnYV57XFxPbWVnYV5ZfSJdLFswLDEsIlkiXSxbMiwwLCJYXFx0aW1lcyBcXE9tZWdhXlgiXSxbNCwwLCJcXE9tZWdhXntcXGxlZnQoXFxPbWVnYV5YXFxyaWdodCl9Il0sWzQsMSwiXFxPbWVnYV57XFxPbWVnYV57XFxsZWZ0KFxcT21lZ2FeWFxccmlnaHQpfX0iXSxbNCwyLCJcXE9tZWdhXntcXGxlZnQoXFxPbWVnYV5YXFxyaWdodCl9Il0sWzMsMywiXFxPbWVnYV57WH1cXHRpbWVzIFgiXSxbMSw3LCJcXE9tZWdhXlhcXHRpbWVzIFgiXSxbMCw1LCJcXE9tZWdhXntcXE9tZWdhXntcXE9tZWdhXlh9fVxcdGltZXMgWCJdLFszLDgsIlxcT21lZ2EiXSxbMiw2LCJcXE9tZWdhXntcXE9tZWdhXntcXE9tZWdhXlh9fVxcdGltZXMgXFxPbWVnYV57XFxPbWVnYV5YfSJdLFszLDUsIlxcT21lZ2FeWFxcdGltZXNcXE9tZWdhXntcXE9tZWdhXlh9Il0sWzQsNiwiXFxPbWVnYV57XFxPbWVnYV5YfVxcdGltZXNcXE9tZWdhXlgiXSxbNCw1LCJYXFx0aW1lc1xcT21lZ2FeWCJdLFs3LDUsIlxcT21lZ2FeWFxcdGltZXMgWCJdLFsyLDMsImV2Il0sWzAsMSwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9IiwxXSxbNCwzLCJldiIsMl0sWzEsNSwiXFxPbWVnYV57XFxPbWVnYV5mfSJdLFswLDYsImYiLDJdLFs2LDUsIlxcbGFtYmRhX3tcXGJldGFcXGdnIGV2fSIsMl0sWzcsMiwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lcyBpZF97XFxPbWVnYV5YfSIsMV0sWzcsNCwiXFxiZXRhIiwyXSxbOCw5LCJcXGxhbWJkYV97XFxiZXRhXFxnZyBldn0iXSxbOSwxMCwiXFxPbWVnYV57XFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9fSJdLFs4LDEwLCJpZCIsMix7ImN1cnZlIjozfV0sWzExLDEzLCJcXGxhbWJkYV97XFxiZXRhXFxnZyBldn1cXHRpbWVzIGlkIiwxXSxbMTMsMTIsIlxcT21lZ2Fee1xcbGFtYmRhX3tcXGJldGEgXFxnZyBldn19XFx0aW1lcyBpZCIsMV0sWzEyLDE0LCJldiIsMV0sWzEzLDE1LCJpZCBcXHRpbWVzIFxcbGFtYmRhX3tcXGJldGEgXFxnZyBldn0iLDFdLFsxNSwxNCwiZXYiLDFdLFsxMSwxNSwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lc1xcbGFtYmRhX3tcXGJldGFcXGdnIGV2fSIsMV0sWzExLDE2LCJpZFxcdGltZXNcXGxhbWJkYV97XFxiZXRhXFxnZyBldn0iLDFdLFsxNiwxNSwiXFxsYW1iZGFfe1xcYmV0YVxcZ2cgZXZ9XFx0aW1lcyBpZCIsMV0sWzE2LDE3LCJcXGJldGEiLDFdLFsxNywxNCwiZXYiLDFdLFsxMSwxOCwiXFxiZXRhIiwxXSxbMTgsMTcsIlxcbGFtYmRhX3tcXGJldGFcXGdnIGV2fVxcdGltZXMgaWQiLDFdLFsxOCwxOSwiXFxiZXRhIiwxXSxbMTksMTQsImV2IiwxXSxbMTEsMTksImlkIl1d
-/
lemma CartesianClosed.internalHom.right_triangle_components
    [BraidedCategory C] (X Y : C) :
    (internalHom.unit X).app ((internalHom.obj (Opposite.op Y)).obj X) ≫
    (internalHom.map ((internalHom.counit X).app _)).app _ = 𝟙 _ := by
  simp only [Functor.id_obj, Functor.comp_obj, Functor.unop_obj, Functor.flip_obj_obj, opOp_obj,
    unit_app, counit_app]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_internalHom_map_app,
    whisker_exchange_assoc, ← uncurry_eq, uncurry_curry,
    BraidedCategory.braiding_naturality_left_assoc,← uncurry_eq, uncurry_curry,
    SymmetricCategory.symmetry_assoc]
  simp [internalHom.obj_obj, uncurry_id_eq_ev]

def CartesianClosed.internalHom.flip_adjoint [CartesianMonoidalCategory C]
    [BraidedCategory C] [CartesianClosed C] (X : C) :
    (internalHom.flip.obj X ⋙ opOp C).unop ⊣ (internalHom.flip.obj X) where
  unit := internalHom.unit X
  counit := internalHom.counit X
  left_triangle_components Y := congr($(internalHom.right_triangle_components X Y).op)
  right_triangle_components Y := internalHom.right_triangle_components X Y.unop


end CategoryTheory
