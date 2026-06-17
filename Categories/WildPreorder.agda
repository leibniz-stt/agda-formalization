{-# OPTIONS --cubical --guardedness --lossy-unification #-}

{-

This file contains a defintion of 'wild preorders' and J/univalence
for these. These are simply wild categories without equations.

Since the defintiion of a functor of wild cats does not mention any
other structure than that mentioned of a wild preorders these are
often a more suitable framework. In particular, if a wild functor F :
C → D is an euqivalence of of wild (univalent) categories (in the
naive sense), this won't imply that C = D. However, we do get that ⌈ C
⌉ = ⌈ D ⌉ where ⌈_⌉ is the forgetful functor WildCat → WildPreorder .

-}
module Categories.WildPreorder where


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

-- To make the coming proofs more convenient, we define wild preorders
-- using Σ types instead of records. In the future, the Cubical
-- library should define a wild cat as wild peorder + equations.
WildPreorder : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
WildPreorder ℓ ℓ' =
  Σ[ ob ∈ Type ℓ ] Σ[ hom ∈ (ob → ob → Type ℓ') ]
      ((x : ob) → hom x x)
    × ((x y z : ob) → hom x y → hom y z → hom x z)

-- Fields
module _ (C : WildPreorder ℓ₁ ℓ₂) where
  obʷᵖ = fst C
  homʷᵖ = fst (snd C)
  idʷᵖ = fst (snd (snd C))
  compʷᵖ = snd (snd (snd C))

-- Forgetful map from wild cats wild preorders
⌈_⌉ : WildCat ℓ₁ ℓ₂ → WildPreorder ℓ₁ ℓ₂
⌈_⌉ C .fst = ob C
⌈_⌉ C .snd .fst = C [_,_]
⌈_⌉ C .snd .snd .fst _ = WildCat.id C
⌈_⌉ C .snd .snd .snd _ _ _ = WildCat._⋆_ C

-- Opposite wild preorders
_^opʷᵖ : WildPreorder ℓ₁ ℓ₂ → WildPreorder ℓ₁ ℓ₂
((obC , homC , idC , compC) ^opʷᵖ) .fst = obC
((obC , homC , idC , compC) ^opʷᵖ) .snd .fst x y = homC y x
((obC , homC , idC , compC) ^opʷᵖ) .snd .snd .fst = idC
((obC , homC , idC , compC) ^opʷᵖ) .snd .snd .snd x y z g f = compC z y x f g

-- A bare notion of functor, not respecting structure
preWPFunctor : WildPreorder ℓ₁ ℓ₂ → WildPreorder ℓ₃ ℓ₄ → Type _
preWPFunctor (obA , homA , idA , compA) (obB , homB , idB , compB) =
  Σ[ f ∈ (obA → obB) ]
    (((x y : obA) → homA x y → homB (f x) (f y)))

-- The structure of a functor of wild preorders
hasWPFunctorStr : (C : WildPreorder ℓ₁ ℓ₂) (D : WildPreorder ℓ₃ ℓ₄)
  → (f : fst C → fst D)
  → Type _
hasWPFunctorStr C D f =
  Σ[ f⃗ ∈ ({x y : obʷᵖ C} → homʷᵖ C x y → homʷᵖ D (f x) (f y)) ]
     (((x : obʷᵖ C) → f⃗ (idʷᵖ C x) ≡ idʷᵖ D (f x))
   × ({x y z : obʷᵖ C} (F : homʷᵖ C x y) (G : homʷᵖ C y z)
   → f⃗ (compʷᵖ C _ _ _ F G ) ≡ compʷᵖ D _ _ _ (f⃗ F) (f⃗ G)))

-- Functors of wild preorders (same definition as functors of wild cats)
WPFunctor : WildPreorder ℓ₁ ℓ₂ → WildPreorder ℓ₃ ℓ₄ → Type _
WPFunctor A B = Σ[ f ∈ _ ] (hasWPFunctorStr A B f)

-- isEquiv predicate
isEquivWPFunctor : (A : WildPreorder ℓ₁ ℓ₂) (B : WildPreorder ℓ₃ ℓ₄)
  → WPFunctor A B → Type _
isEquivWPFunctor A B (f , g , _ , _) = isEquiv f × ((x y : _) → isEquiv (g {x = x} {y}))

-- type of equivalences of wild preorders
_≅ᵂᴾ_ : WildPreorder ℓ₁ ℓ₂ → WildPreorder ℓ₃ ℓ₄ → Type _
A ≅ᵂᴾ B = Σ[ F ∈ WPFunctor A B ] (isEquivWPFunctor A B F)

-- Identity functor
IdWPFunctor : (A : WildPreorder ℓ₁ ℓ₂) → WPFunctor A A
IdWPFunctor A .fst = idfun _
IdWPFunctor A .snd .fst = idfun _
IdWPFunctor A .snd .snd .fst _ = refl
IdWPFunctor A .snd .snd .snd F G = refl

-- Identity equivalence
IdWPEquiv : (A : WildPreorder ℓ₁ ℓ₂) → A ≅ᵂᴾ A
IdWPEquiv A .fst = IdWPFunctor A
IdWPEquiv A .snd .fst = idIsEquiv _
IdWPEquiv A .snd .snd _ _ = idIsEquiv _

-- Proof that total space of ≅ᵂᴾ is contracitble.
isContrTot≅ᵂᴾ : (A : WildPreorder ℓ₁ ℓ₂)
  → isContr (Σ[ A' ∈ WildPreorder ℓ₁ ℓ₂ ] (A ≅ᵂᴾ A'))
isContrTot≅ᵂᴾ A .fst = A , IdWPEquiv A
isContrTot≅ᵂᴾ {ℓ₁ = ℓ₁} {ℓ₂} (obA , homA , idA , compA) .snd =
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
  shuffle : Iso (Σ[ A' ∈ WildPreorder ℓ₁ ℓ₂ ]
                  ((obA , homA , idA , compA) ≅ᵂᴾ A'))
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

-- J rule for wild preorders
JWildPreorder : {A : WildPreorder ℓ₁ ℓ₂}
  (P : (A' : WildPreorder ℓ₁ ℓ₂) → A ≅ᵂᴾ A' → Type ℓ₃)
  (e : P A (IdWPEquiv A))
    → (A' : _) (e : _) → P A' e
JWildPreorder P idp A' e =
  subst (λ x → P (fst x) (snd x)) (isContrTot≅ᵂᴾ _ .snd (A' , e)) idp

-- Univalence
univalenceWildPreorder : ∀ {A B : WildPreorder ℓ₁ ℓ₂} → (A ≡ B) ≃ (A ≅ᵂᴾ B)
univalenceWildPreorder =
  fundamentalTheoremOfId _≅ᵂᴾ_ IdWPEquiv isContrTot≅ᵂᴾ _ _

-- Univalence: β-rule
univalenceWildPreorderRefl : {A : WildPreorder ℓ₁ ℓ₂}
  → fst (univalenceWildPreorder {A = A}) refl ≡ IdWPEquiv A
univalenceWildPreorderRefl =
  fundamentalTheoremOfIdβ _≅ᵂᴾ_ IdWPEquiv isContrTot≅ᵂᴾ _

-- Univalence: β-rule, other direction
univalence⁻IdWPEquiv : {A : WildPreorder ℓ₁ ℓ₂}
  → invEq (univalenceWildPreorder {A = A}) (IdWPEquiv A) ≡ refl
univalence⁻IdWPEquiv {A = A} =
  cong (invEq univalenceWildPreorder) (sym (univalenceWildPreorderRefl {A = A}))
  ∙ retEq univalenceWildPreorder refl


---------- Bicats ------------
-- Bifunctor structure
record hasBiWPFunctorStructure
  (C : WildPreorder ℓ₁ ℓ₂) (D : WildPreorder ℓ₃ ℓ₄) (E : WildPreorder ℓ₅ ℓ₆)
  (_⊗_ : fst C → fst D → fst E)
  : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ (ℓ-max ℓ₃ (ℓ-max ℓ₄ (ℓ-max ℓ₅ ℓ₆))))) where
  field
    leftAct : (d : obʷᵖ D) → hasWPFunctorStr C E (_⊗ d)
    rightAct : (c : obʷᵖ C) → hasWPFunctorStr D E (c ⊗_)

-- For completeness, here's a defintion of a naive isomorphism of wild cats
-- and a proof that it coincides with equivalence of underlying pro-wild cats
isNaiveIso : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → WildFunctor C D → Type _
isNaiveIso F = isEquiv (WildFunctor.F-ob F)
             × ((x y : _) → isEquiv (WildFunctor.F-hom F {x = x} {y}))

_≅ᵂ_ : WildCat ℓ₁ ℓ₂ →  WildCat ℓ₃ ℓ₄ → Type _
C ≅ᵂ D = Σ[ F ∈ WildFunctor C D ] isNaiveIso F

≅ᵂᴾ→≅ᵂ : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → ⌈ C ⌉ ≅ᵂᴾ ⌈ D ⌉ → C ≅ᵂ D
≅ᵂᴾ→≅ᵂ F .fst .WildFunctor.F-ob = fst (fst F)
≅ᵂᴾ→≅ᵂ F .fst .WildFunctor.F-hom = F .fst .snd .fst
≅ᵂᴾ→≅ᵂ F .fst .WildFunctor.F-id = F .fst .snd .snd .fst _
≅ᵂᴾ→≅ᵂ F .fst .WildFunctor.F-seq = F .fst .snd .snd .snd
≅ᵂᴾ→≅ᵂ F .snd = F .snd

≅ᵂ→≅ᵂᴾ : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → C ≅ᵂ D → ⌈ C ⌉ ≅ᵂᴾ ⌈ D ⌉
≅ᵂ→≅ᵂᴾ F .fst .fst = F .fst .WildFunctor.F-ob
≅ᵂ→≅ᵂᴾ F .fst .snd .fst = F .fst .WildFunctor.F-hom
≅ᵂ→≅ᵂᴾ F .fst .snd .snd .fst _ = F .fst .WildFunctor.F-id
≅ᵂ→≅ᵂᴾ F .fst .snd .snd .snd = F .fst .WildFunctor.F-seq
≅ᵂ→≅ᵂᴾ F .snd = F .snd

Equiv-≅ᵂ-≅ᵂᴾ : {C : WildCat ℓ₁ ℓ₂} {D : WildCat ℓ₃ ℓ₄}
  → (C ≅ᵂ D) ≃ (⌈ C ⌉ ≅ᵂᴾ ⌈ D ⌉)
Equiv-≅ᵂ-≅ᵂᴾ = isoToEquiv (iso ≅ᵂ→≅ᵂᴾ ≅ᵂᴾ→≅ᵂ
  (λ _ → refl)
  retr)
  where
  retr : retract ≅ᵂ→≅ᵂᴾ ≅ᵂᴾ→≅ᵂ
  retr F i .fst .WildFunctor.F-ob = F .fst .WildFunctor.F-ob
  retr F i .fst .WildFunctor.F-hom = F .fst .WildFunctor.F-hom
  retr F i .fst .WildFunctor.F-id = F .fst .WildFunctor.F-id
  retr F i .fst .WildFunctor.F-seq = F .fst .WildFunctor.F-seq
  retr F i .snd = F .snd
