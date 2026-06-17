{-# OPTIONS --cubical --guardedness --lossy-unification #-}
{-
This file constructs Map as a wild category (𝑴𝑨𝑷). It also proves
J/univalence for this category.
-}
module Categories.Map where

-- Local imports
open import Prelude
open import Categories.WildPreorder

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.WildCat.Base

open WildCat hiding (_∘_) renaming (_⋆_ to cC)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- The type of maps (wild arrow category over the universe)
Map : (ℓ : Level) → Type (ℓ-suc ℓ)
Map ℓ = Σ[ A ∈ Type ℓ ] Σ[ B ∈ Type ℓ ] (A → B)

Dom : Map ℓ₁ → Type ℓ₁
Dom = fst

Cod : Map ℓ₁ → Type ℓ₁
Cod A = fst (snd A)

_⃗ : (A : Map ℓ₁) → Dom A → Cod A
((_ , _ , f) ⃗) = f

⦅_⦆ : ∀ {A B : Type ℓ₁} (f : A → B) → Map _
⦅ f ⦆ = _ , (_ , f)

-- Hom types
Map[_,_] : (D : Map ℓ₁) (E : Map ℓ₂)
  → Type _
Map[_,_] (A , B , f) (A' , B' , f') =
  Σ[ α ∈ (A → A') ] Σ[ β ∈ (B → B') ] ((β ∘ f) ∼ (f' ∘ α))

-- Composition
compHomMap : (C : Map ℓ₁) (D : Map ℓ₂)
  (E : Map ℓ₃) → Map[ C , D ] → Map[ D , E ]
  → Map[ C , E ]
compHomMap _ _ _ (α , β , p) (α' , β' , q) .fst = α' ∘ α
compHomMap _ _ _ (α , β , p) (α' , β' , q) .snd .fst = β' ∘ β
compHomMap _ _ _ (α , β , p) (α' , β' , q) .snd .snd x = cong β' (p x) ∙ q (α x)

-- Identity
idHomMap : {C : Map ℓ₁} → Map[ C , C ]
idHomMap .fst = idfun _
idHomMap .snd .fst = idfun _
idHomMap .snd .snd x = refl

-- Associativity
assocMap : {C : Map ℓ₁} {D : Map ℓ₂}
  {E : Map ℓ₃} {K : Map ℓ₄}
  (F : Map[ C , D ]) (G : Map[ D , E ]) (H : Map[ E , K ])
  → compHomMap C E K (compHomMap C D E F G) H
   ≡ compHomMap C D K F (compHomMap D E K  G H)
assocMap (α , β , p) (α' , β' , q) (α'' , β'' , r) =
  ΣPathP (refl , ΣPathP (refl
  , funExt λ c →
    cong (_∙ r (α' (α c)))
         ( (cong-∙ β'' (cong β' (p c)) (q (α c))))
  ∙ sym (assoc (cong (β'' ∘ β') (p c)) (cong β'' (q (α c))) (r (α' (α c))))))

-- Unit laws
module _ {C : Map ℓ₁} {D : Map ℓ₂} (F : Map[ C , D ]) where
  MapIdL : compHomMap C C D (idHomMap {C = C}) F ≡ F
  MapIdL = ΣPathP (refl , (ΣPathP (refl , funExt λ x → sym (lUnit _))))

  MapIdR : compHomMap C D D F (idHomMap {C = D}) ≡ F
  MapIdR = ΣPathP (refl , (ΣPathP (refl , funExt λ x → sym (rUnit _))))

-- The category
𝑴𝑨𝑷 : (ℓ : Level) → WildCat (ℓ-suc ℓ) ℓ
𝑴𝑨𝑷 ℓ .ob = Map ℓ
𝑴𝑨𝑷 ℓ .Hom[_,_] A B = Map[_,_] A B
𝑴𝑨𝑷 ℓ .WildCat.id = idHomMap
𝑴𝑨𝑷 ℓ .cC {x = x} {y} {z} = compHomMap x y z
𝑴𝑨𝑷 ℓ .⋆IdL {x = x} {y} = MapIdL {C = x} {y}
𝑴𝑨𝑷 ℓ .⋆IdR {x = x} {y} = MapIdR {C = x} {y}
𝑴𝑨𝑷 ℓ .⋆Assoc {u = u} {v} {x} {y} f g h =
  assocMap {C = u} {v} {x} {y} f g h

-------- Univalence and J --------

-- Equivalence of objects
_≃Map_ : {ℓ₁ ℓ₂ : Level} → Map ℓ₁ → Map ℓ₂ → Type _
(A , B , f) ≃Map (X , Y , g) =
  Σ[ e1 ∈ A ≃ X ] Σ[ e2 ∈ B ≃ Y ] ((a : A) → fst e2 (f a) ≡ g (fst e1 a))

-- Identity equivalence
IdMapEquiv : {ℓ₁ : Level} (A : Map ℓ₁) → A ≃Map A
IdMapEquiv A .fst = idEquiv _
IdMapEquiv A .snd .fst = idEquiv _
IdMapEquiv A .snd .snd _ = refl

-- Total space of ≃Map is contractible
isContrTot≃Map : (A : Map ℓ₁) → isContr (Σ[ B ∈ Map ℓ₁ ] (A ≃Map B))
fst (isContrTot≃Map A) = A , IdMapEquiv A
snd (isContrTot≃Map A) = lem _
  where
  lem : isProp (Σ[ B ∈ Map _ ] (A ≃Map B))
  lem = isOfHLevelRetractFromIso 1
    (compIso Σ-assoc-Iso
     (compIso (Σ-cong-iso-snd
       (λ A' → compIso (invIso Σ-assoc-Iso)
                (compIso (invIso (Σ-cong-iso-fst Σ-swap-Iso))
                 Σ-assoc-Iso)))
      (compIso (invIso Σ-assoc-Iso)
       (compIso (Σ-cong-iso-snd λ Ae
        → compIso Σ-assoc-Iso (compIso (Σ-cong-iso-snd
            (λ B → compIso (invIso Σ-assoc-Iso)
            (compIso (invIso (Σ-cong-iso-fst Σ-swap-Iso)) Σ-assoc-Iso)))
        (invIso Σ-assoc-Iso)))
        (compIso (Σ-contractFstIso (isContrTot≃ (A .fst)))
          (compIso (Σ-contractFstIso (isContrTot≃ (A .snd .fst)))
           (Σ-cong-iso-snd (λ _ → funExtIso))))))))
        (isContr→isProp (isContrSingl (A .snd .snd)))

-- J rule
JMap : {A : Map ℓ₁} (P : (A' : Map ℓ₁) → A ≃Map A' → Type ℓ₂)
                    (e : P A (IdMapEquiv A))
    → (A' : _) (e : _) → P A' e
JMap {A = A} P idp A' e' =
  subst (λ x → P (fst x) (snd x))
    (isContrTot≃Map A .snd (A' , e')) idp

-- Univalence
univalenceMap : ∀ {A B : Map ℓ₁} → (A ≡ B) ≃ (A ≃Map B)
univalenceMap =
  fundamentalTheoremOfId _≃Map_ IdMapEquiv isContrTot≃Map _ _

-- Univalence: β rule
univalenceMapRefl : {A : Map ℓ₁} → fst (univalenceMap {A = A}) refl ≡ IdMapEquiv A
univalenceMapRefl = fundamentalTheoremOfIdβ _≃Map_ IdMapEquiv isContrTot≃Map _

-- Univalence: β rule, other way around
univalence⁻IdMapEquiv : {A : Map ℓ₁} → invEq (univalenceMap {A = A}) (IdMapEquiv A) ≡ refl
univalence⁻IdMapEquiv {A = A} =
  cong (invEq univalenceMap) (sym (univalenceMapRefl {A = A}))
  ∙ retEq univalenceMap refl

----- Other constructions -----
-- isEquiv as a predicate on Map
isEquivMap : Map ℓ₁ → Type ℓ₁
isEquivMap (A , B , f) = isEquiv f

-- identity function as an element of Map
idMap : (A : Type ℓ₁) → Map ℓ₁
idMap A = A , A , idfun A


-- retracts in Map
retractMap : (f g : Map ℓ₁) → Type ℓ₁
retractMap f g =
  Σ[ F ∈ Map[ f , g ] ]
    Σ[ G ∈ Map[ g , f ] ]
      (compHomMap f _ f F G ≡ idHomMap {C = f})

-- retracts of equivalences are equivalences
retrEquivMap : (i j : Map ℓ₁) → isEquivMap i → retractMap j i → isEquivMap j
retrEquivMap (A , B , e') (α , β , r) e ((m1 , m2 , p) , (m3 , m4 , q) , ps) =
  isoToIsEquiv
   (iso _ (m3 ∘ invEq (_ , e) ∘ m2)
          (λ x → sym (q (invEq (_ , e) (m2 x)))
                ∙ cong m4 (secEq (_ , e) (m2 x))
                ∙ funExt⁻ (cong (fst ∘ snd) ps) x)
          (λ x → cong (m3 ∘ invEq (_ , e)) (p x)
                ∙ cong m3 (retEq (_ , e) (m1 x))
                ∙ funExt⁻ (cong fst ps) x))
