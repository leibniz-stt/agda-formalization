{-# OPTIONS --cubical --guardedness --lossy-unification #-}

{-

This file contains a defintion of 'proto-wild cats' and J/univalence
for these. These are simply wild categories without equations.

Since the defintiion of a functor of wild cats does not mention any
other structure than that mentioned of a proto-wild category, these
are often a more suitable framework. In particular, if a wild functor
F : C → D is an equivalence of wild (univalent) categories, this won't
imply that C = D. However, we do get that ⌈ C ⌉ = ⌈ D ⌉ where ⌈_⌉ is
the forgetful functor WildCat → ProtoWildCat .

-}
module Categories.ProtoWildCat where


-- Local imports
open import Prelude

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

open WildCat hiding (_∘_)
open Iso

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

  _⋄_ = compIso

-- To make the coming proofs more convenient, we define proto wild
-- cats using Σ types instead of records. In the future, the Cubical
-- library should define a wild cat as a proto-wild cat + equations.
ProtoWildCat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ProtoWildCat ℓ ℓ' =
  Σ[ ob ∈ Type ℓ ] Σ[ hom ∈ (ob → ob → Type ℓ') ]
      ((x : ob) → hom x x)
    × ((x y z : ob) → hom x y → hom y z → hom x z)

-- Fields
module _ (C : ProtoWildCat ℓ₁ ℓ₂) where
  obᵖʳ = fst C
  homᵖʳ = fst (snd C)
  idᵖʳ = fst (snd (snd C))
  compᵖʳ = snd (snd (snd C))

-- Forgetful map from wild cats to proto-wild cats
⌈_⌉ : WildCat ℓ₁ ℓ₂ → ProtoWildCat ℓ₁ ℓ₂
⌈_⌉ C .fst = ob C
⌈_⌉ C .snd .fst = C [_,_]
⌈_⌉ C .snd .snd .fst _ = WildCat.id C
⌈_⌉ C .snd .snd .snd _ _ _ = WildCat._⋆_ C

-- Opposite proto-wild cats
_^opᵖʳ : ProtoWildCat ℓ₁ ℓ₂ → ProtoWildCat ℓ₁ ℓ₂
((obC , homC , idC , compC) ^opᵖʳ) .fst = obC
((obC , homC , idC , compC) ^opᵖʳ) .snd .fst x y = homC y x
((obC , homC , idC , compC) ^opᵖʳ) .snd .snd .fst = idC
((obC , homC , idC , compC) ^opᵖʳ) .snd .snd .snd x y z g f = compC z y x f g

-- A bare notion of functor, not respecting structure
preProtoWildFunctor : ProtoWildCat ℓ₁ ℓ₂ → ProtoWildCat ℓ₃ ℓ₄ → Type _
preProtoWildFunctor (obA , homA , idA , compA) (obB , homB , idB , compB) =
  Σ[ f ∈ (obA → obB) ]
    (((x y : obA) → homA x y → homB (f x) (f y)))

-- The structure of a functor of proto cats
hasProtoFunctorStr : (C : ProtoWildCat ℓ₁ ℓ₂) (D : ProtoWildCat ℓ₃ ℓ₄)
  → (f : fst C → fst D)
  → Type _
hasProtoFunctorStr C D f =
  Σ[ f⃗ ∈ ({x y : obᵖʳ C} → homᵖʳ C x y → homᵖʳ D (f x) (f y)) ]
     (((x : obᵖʳ C) → f⃗ (idᵖʳ C x) ≡ idᵖʳ D (f x))
   × ({x y z : obᵖʳ C} (F : homᵖʳ C x y) (G : homᵖʳ C y z)
   → f⃗ (compᵖʳ C _ _ _ F G ) ≡ compᵖʳ D _ _ _ (f⃗ F) (f⃗ G)))

-- Functors of proto wild cats (same definition as functors of wild cats)
ProtoWildFunctor : ProtoWildCat ℓ₁ ℓ₂ → ProtoWildCat ℓ₃ ℓ₄ → Type _
ProtoWildFunctor A B = Σ[ f ∈ _ ] (hasProtoFunctorStr A B f)

-- isEquiv predicate
isEquivProtoWildFunctor : (A : ProtoWildCat ℓ₁ ℓ₂) (B : ProtoWildCat ℓ₃ ℓ₄)
  → ProtoWildFunctor A B → Type _
isEquivProtoWildFunctor A B (f , g , _ , _) = isEquiv f × ((x y : _) → isEquiv (g {x = x} {y}))

-- type of equivalences of proto-wild cats
_≅ᴾᵂ_ : ProtoWildCat ℓ₁ ℓ₂ → ProtoWildCat ℓ₃ ℓ₄ → Type _
A ≅ᴾᵂ B = Σ[ F ∈ ProtoWildFunctor A B ] (isEquivProtoWildFunctor A B F)

-- Identity proto-functor
IdProtoWildFunctor : (A : ProtoWildCat ℓ₁ ℓ₂) → ProtoWildFunctor A A
IdProtoWildFunctor A .fst = idfun _
IdProtoWildFunctor A .snd .fst = idfun _
IdProtoWildFunctor A .snd .snd .fst _ = refl
IdProtoWildFunctor A .snd .snd .snd F G = refl

-- Identity proto-equiv
IdProtoWildEquiv : (A : ProtoWildCat ℓ₁ ℓ₂) → A ≅ᴾᵂ A
IdProtoWildEquiv A .fst = IdProtoWildFunctor A
IdProtoWildEquiv A .snd .fst = idIsEquiv _
IdProtoWildEquiv A .snd .snd _ _ = idIsEquiv _

-- Proof that total space of ≅ᴾᵂ is contracitble.
isContrTot≅ᴾᵂ : (A : ProtoWildCat ℓ₁ ℓ₂)
  → isContr (Σ[ A' ∈ ProtoWildCat ℓ₁ ℓ₂ ] (A ≅ᴾᵂ A'))
isContrTot≅ᴾᵂ A .fst = A , IdProtoWildEquiv A
isContrTot≅ᴾᵂ {ℓ₁ = ℓ₁} {ℓ₂} (obA , homA , idA , compA) .snd =
  isContr→isProp (isOfHLevelRetractFromIso 0
    ((shuffle
    ⋄ equivToIso (Σ-contractFst (isContrTot≃ _)))
    ⋄ (equivToIso (Σ-contractFstIso' (isOfHLevelRetractFromIso 0
       (Σ-cong-iso-snd (λ homA' → compIso (invIso curryIso)
        (compIso (codomainIsoDep λ f → equivToIso (invEquiv univalence))
          (compIso (compIso curryIso
            (codomainIsoDep λ a → funExtIso))
            funExtIso))))
       (isContrSingl homA)) (homA , (λ _ _ → idEquiv _)))))
    (isContrΣ (isContrSingl _) λ _ → isContrSingl _)) _
  where
  shuffle : Iso (Σ[ A' ∈ ProtoWildCat ℓ₁ ℓ₂ ]
                  ((obA , homA , idA , compA) ≅ᴾᵂ A'))
             (Σ[ p1 ∈ (Σ[ obA' ∈ Type ℓ₁ ] obA ≃ obA') ]
               Σ[ p2 ∈ (Σ[ homA' ∈ ((x y : fst p1) → Type ℓ₂) ]
                 (((x y : obA) → homA x y ≃ homA' (fst (snd p1) x)
                                                  (fst (snd p1) y)))) ]
                   (Σ[ idA' ∈ ((x : p1 .fst) → p2 .fst x x) ]
                                  ((λ x → fst (p2 .snd x x) (idA x))
                                 ≡ idA' ∘ fst (snd p1)))
                 × (Σ[ compA' ∈ ((x y z : p1 .fst)
                              → (p2 .fst x y)
                              → (p2 .fst y z)
                              → (p2 .fst x z)) ]
                   (λ x y z (f : homA x y) (g : homA y z)
                   → snd p2 _ _ .fst (compA _ _ _ f g))
                 ≡ λ (x y z : obA) f g
                   → compA' _ _ _ (fst (snd p2 x y) f) (fst (snd p2 y z) g)))
  shuffle .fun ((obA' , homA' , idA' , compA') , (e1 , e2 , e3 , e4) , (e5 , e6)) =
    (obA' , e1 , e5) , (homA' , (λ x y → e2 {x = x} {y} , e6 x y))
    , ((idA' , funExt e3) , (compA' , λ i x y z f g → e4 {x = x} {y} {z} f g i))
  shuffle .inv ((a , b) , (c , d) , (e , f) , (g , h)) =
    (a , (c , (e , g))) , (b .fst , (λ f → d _ _ .fst f)
       , (λ x i → f i x)
       , λ F G i → h i _ _ _ F G)
       , (b .snd) , λ x y → d x y .snd
  shuffle .sec _ = refl
  shuffle .ret _ = refl

-- J rule for proto-wild cats
JProtoWildCat : {A : ProtoWildCat ℓ₁ ℓ₂}
  (P : (A' : ProtoWildCat ℓ₁ ℓ₂) → A ≅ᴾᵂ A' → Type ℓ₃)
  (e : P A (IdProtoWildEquiv A))
    → (A' : _) (e : _) → P A' e
JProtoWildCat P idp A' e =
  subst (λ x → P (fst x) (snd x)) (isContrTot≅ᴾᵂ _ .snd (A' , e)) idp

-- Univalence
univalenceProtoWildCat : ∀ {A B : ProtoWildCat ℓ₁ ℓ₂} → (A ≡ B) ≃ (A ≅ᴾᵂ B)
univalenceProtoWildCat =
  fundamentalTheoremOfId _≅ᴾᵂ_ IdProtoWildEquiv isContrTot≅ᴾᵂ _ _

-- Univalence: β-rule
univalenceProtoWildCatRefl : {A : ProtoWildCat ℓ₁ ℓ₂}
  → fst (univalenceProtoWildCat {A = A}) refl ≡ IdProtoWildEquiv A
univalenceProtoWildCatRefl =
  fundamentalTheoremOfIdβ _≅ᴾᵂ_ IdProtoWildEquiv isContrTot≅ᴾᵂ _

-- Univalence: β-rule, other direction
univalence⁻IdProtoWildEquiv : {A : ProtoWildCat ℓ₁ ℓ₂}
  → invEq (univalenceProtoWildCat {A = A}) (IdProtoWildEquiv A) ≡ refl
univalence⁻IdProtoWildEquiv {A = A} =
  cong (invEq univalenceProtoWildCat) (sym (univalenceProtoWildCatRefl {A = A}))
  ∙ retEq univalenceProtoWildCat refl


---------- Bicats ------------
-- Bifunctor structure
record hasBiProtoFunctorStructure
  (C : ProtoWildCat ℓ₁ ℓ₂) (D : ProtoWildCat ℓ₃ ℓ₄) (E : ProtoWildCat ℓ₅ ℓ₆)
  (_⊗_ : fst C → fst D → fst E)
  : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ (ℓ-max ℓ₃ (ℓ-max ℓ₄ (ℓ-max ℓ₅ ℓ₆))))) where
  field
    leftAct : (d : obᵖʳ D) → hasProtoFunctorStr C E (_⊗ d)
    rightAct : (c : obᵖʳ C) → hasProtoFunctorStr D E (c ⊗_)

-- For completeness, here's a defintion of equivalence of wild cats
-- and a proof that it coincides with equivalence of underlying pro-wild cats
isWildEquiv : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → WildFunctor C D → Type _
isWildEquiv F = isEquiv (WildFunctor.F-ob F)
             × ((x y : _) → isEquiv (WildFunctor.F-hom F {x = x} {y}))

_≃ᵂ_ : WildCat ℓ₁ ℓ₂ →  WildCat ℓ₃ ℓ₄ → Type _
C ≃ᵂ D = Σ[ F ∈ WildFunctor C D ] isWildEquiv F

≅ᴾᵂ→≃ᵂ : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → ⌈ C ⌉ ≅ᴾᵂ ⌈ D ⌉ → C ≃ᵂ D
≅ᴾᵂ→≃ᵂ F .fst .WildFunctor.F-ob = fst (fst F)
≅ᴾᵂ→≃ᵂ F .fst .WildFunctor.F-hom = F .fst .snd .fst
≅ᴾᵂ→≃ᵂ F .fst .WildFunctor.F-id = F .fst .snd .snd .fst _
≅ᴾᵂ→≃ᵂ F .fst .WildFunctor.F-seq = F .fst .snd .snd .snd
≅ᴾᵂ→≃ᵂ F .snd = F .snd

≃ᵂ→≅ᴾᵂ : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → C ≃ᵂ D → ⌈ C ⌉ ≅ᴾᵂ ⌈ D ⌉
≃ᵂ→≅ᴾᵂ F .fst .fst = F .fst .WildFunctor.F-ob
≃ᵂ→≅ᴾᵂ F .fst .snd .fst = F .fst .WildFunctor.F-hom
≃ᵂ→≅ᴾᵂ F .fst .snd .snd .fst _ = F .fst .WildFunctor.F-id
≃ᵂ→≅ᴾᵂ F .fst .snd .snd .snd = F .fst .WildFunctor.F-seq
≃ᵂ→≅ᴾᵂ F .snd = F .snd

Equiv-≃ᵂ-≅ᴾᵂ : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → (C ≃ᵂ D) ≃ (⌈ C ⌉ ≅ᴾᵂ ⌈ D ⌉)
Equiv-≃ᵂ-≅ᴾᵂ = isoToEquiv (iso ≃ᵂ→≅ᴾᵂ ≅ᴾᵂ→≃ᵂ
  (λ _ → refl)
  retr)
  where
  retr : retract ≃ᵂ→≅ᴾᵂ ≅ᴾᵂ→≃ᵂ
  retr F i .fst .WildFunctor.F-ob = F .fst .WildFunctor.F-ob
  retr F i .fst .WildFunctor.F-hom = F .fst .WildFunctor.F-hom
  retr F i .fst .WildFunctor.F-id = F .fst .WildFunctor.F-id
  retr F i .fst .WildFunctor.F-seq = F .fst .WildFunctor.F-seq
  retr F i .snd = F .snd
