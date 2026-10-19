/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Bundle

/-!
# Maps of dependent total spaces

A base map `f : B → C` and fiber maps `φ : ∀ b, E b → V (f b)` induce a map from
`Bundle.TotalSpace F E` to `Bundle.TotalSpace G V`. The source and target model parameters
`F` and `G` are independent phantom types: no elements or structures on them are required.
The base, fiber and model types all have independent universes.

The constructor, projection and dependent fiber equations describe this map without transport.
Identity and composition hold on the original total spaces. For identity fiber maps on a
pullback family and the same model on both sides, the map is `Bundle.Pullback.lift`.

## References

Mathlib's `Mathlib.Data.Bundle`, by Nicolò Cavalleri, supplies the total-space structure,
constructor, extensionality, eta and pullback lift. The elementary map and its characteristic
API are by Formal Frontier Agents.
-/

@[expose] public section

universe uB uC uE uV uF uG uD uW uJ

namespace Bundle.TotalSpace

variable {B : Type uB} {C : Type uC} {E : B → Type uE} {V : C → Type uV}

/-- Map dependent total spaces by a base map and a family of fiber maps.
The source model `F` and target model `G` are independent phantom parameters. -/
def map (F : Type uF) (G : Type uG) (f : B → C) (φ : ∀ b, E b → V (f b)) :
    TotalSpace F E → TotalSpace G V :=
  fun p ↦ mk' G (f p.proj) (φ p.proj p.snd)

section Coordinates

variable (F : Type uF) (G : Type uG) (f : B → C) (φ : ∀ b, E b → V (f b))

/-- The total-space map sends each constructor to the corresponding mapped constructor. -/
theorem map_mk (b : B) (x : E b) :
    map F G f φ (mk' F b x) = mk' G (f b) (φ b x) := rfl

/-- The projection of the image is the image of the projection under the base map. -/
theorem map_proj (p : TotalSpace F E) :
    (map F G f φ p).proj = f p.proj := rfl

/-- The fiber coordinate of the image is given by the fiber map, with no index transport. -/
theorem map_snd (p : TotalSpace F E) :
    (map F G f φ p).snd = φ p.proj p.snd := rfl

end Coordinates

/-- Identity base and fiber maps give the identity on the same total space and model. -/
theorem map_id (F : Type uF) :
    map (E := E) (V := E) F F id (fun _ ↦ id) = id := rfl

/-- Total-space maps compose by composing the base maps and the corresponding fiber maps.
The intermediate total space has the same family and model in both factors. -/
theorem map_comp {D : Type uD} {W : D → Type uW}
    (F : Type uF) (G : Type uG) (J : Type uJ)
    (f : B → C) (φ : ∀ b, E b → V (f b))
    (g : C → D) (ψ : ∀ c, V c → W (g c)) :
    map G J g ψ ∘ map F G f φ =
      map F J (g ∘ f) (fun b ↦ ψ (f b) ∘ φ b) := rfl

/-- On a pullback family, identity fiber maps with a common model give the pullback lift. -/
theorem map_pullback_eq_lift (G : Type uG) (f : B → C) :
    map (E := Bundle.Pullback f V) (V := V) G G f (fun _ ↦ id) =
      Bundle.Pullback.lift (F := G) (E := V) f := rfl

end Bundle.TotalSpace
