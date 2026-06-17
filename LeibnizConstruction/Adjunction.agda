{-# OPTIONS --cubical --guardedness #-}
{-
This proves the adjunction between Leibniz products and exponentials (on Fam).
-}
module LeibnizConstruction.Adjunction where

-- Local imports
open import Prelude
open import Categories.WildPreorder
open import Categories.Fam
open import LeibnizConstruction.Fam

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout

open Iso

private
  variable
    ℓ₁ ℓ₂ : Level

module _ (AB XY CD : Fam ℓ₁) where
  [⊠ᶠ→○]→[○→⋔ᶠ] : Fam[ AB ⊠ᶠ XY , CD ] → Fam[ AB , XY ⋔ᶠ CD ]
  [⊠ᶠ→○]→[○→⋔ᶠ] (f , g) .fst a .fst z = f (a , z)
  [⊠ᶠ→○]→[○→⋔ᶠ] (f , g) .fst a .snd x y = g (a , x) (inr y)
  [⊠ᶠ→○]→[○→⋔ᶠ] (f , g) .snd a b x .fst = g (a , x) (inl b)
  [⊠ᶠ→○]→[○→⋔ᶠ] (f , g) .snd a b x .snd y =
    cong (g (a , x)) (sym (push (b , y)))

  [○→⋔ᶠ]→[⊠ᶠ→○] : Fam[ AB , XY ⋔ᶠ CD ] → Fam[ AB ⊠ᶠ XY , CD ]
  [○→⋔ᶠ]→[⊠ᶠ→○] (f , g) .fst (a , x) = f a .fst x
  [○→⋔ᶠ]→[⊠ᶠ→○] (f , g) .snd (a , x) =
    rec∣inl b ↦ g a b x .fst
       ∣inr y ↦ f a .snd x y
       ∣push (b , y) ↦ sym (g a b x .snd y)

  ⊠ᶠ⊣⋔-Iso : Iso (Fam[ AB ⊠ᶠ XY , CD ]) (Fam[ AB , XY ⋔ᶠ CD ])
  ⊠ᶠ⊣⋔-Iso .fun = [⊠ᶠ→○]→[○→⋔ᶠ]
  ⊠ᶠ⊣⋔-Iso .inv = [○→⋔ᶠ]→[⊠ᶠ→○]
  ⊠ᶠ⊣⋔-Iso .sec (f , g) = refl
  ⊠ᶠ⊣⋔-Iso .ret (f , g) =
    ΣPathP (refl , funExt λ {(x , y) → funExt
     (elim∣inl b ↦ refl
          ∣inr y ↦ refl
          ∣push (b , y) ↦ λ _ → refl)})

-- specialised predicate spelling out what it means for ⊠ and ⋔ to be
-- adjoint. This predicate will be transproted over to Map later

record wildBiAdjoint (C : WildPreorder ℓ₁ ℓ₂)
       (_⊗_ _⋔_ : fst C → fst C → fst C)
       (str⊗ : hasBiWPFunctorStructure C C C _⊗_)
       (str⋔ : hasBiWPFunctorStructure (C ^opʷᵖ) C C _⋔_) : Type (ℓ-max ℓ₁ ℓ₂) where
  open hasBiWPFunctorStructure
  field
    eq : (X Y Z : obʷᵖ C) → homʷᵖ C (X ⊗ Y) Z ≃ homʷᵖ C X (Y ⋔ Z)

    natL : (X X' Y Z : obʷᵖ C) (f : homʷᵖ C X X')
      → fst (eq X Y Z) ∘ compʷᵖ C (X ⊗ Y) (X' ⊗ Y) Z (fst (leftAct str⊗ Y) f)
       ≡ compʷᵖ C X X' (Y ⋔ Z) f ∘ fst (eq X' Y Z)

    natR : (X Y Y' Z : obʷᵖ C) (f : homʷᵖ C Y Y')
      → fst (eq X Y Z)
       ∘ compʷᵖ C (X ⊗ Y) (X ⊗ Y') Z (fst (rightAct str⊗ X) f)
       ≡ (λ g → compʷᵖ C X (Y' ⋔ Z) (Y ⋔ Z) g (fst (leftAct str⋔ Z) f))
        ∘ fst (eq X Y' Z)

    natPost : (X Y Z Z' : obʷᵖ C) (f : homʷᵖ C Z Z')
      → fst (eq X Y Z')
       ∘ (λ g → compʷᵖ C (X ⊗ Y) Z Z' g f)
       ≡ (λ g → compʷᵖ C X (Y ⋔ Z) (Y ⋔ Z') g (fst (rightAct str⋔ Y) f))
        ∘ fst (eq X Y Z)

wildBiAdjoint-⊠ᶠ-⋔ᶠ : wildBiAdjoint ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ _⊠ᶠ_ _⋔ᶠ_
                      hasBiWPFunctorStructure⊠ᶠ
                      hasBiWPFunctorStructure⋔ᶠ
wildBiAdjoint-⊠ᶠ-⋔ᶠ .wildBiAdjoint.eq X Y Z = isoToEquiv (⊠ᶠ⊣⋔-Iso X Y Z)
wildBiAdjoint-⊠ᶠ-⋔ᶠ .wildBiAdjoint.natL _ _ _ _ _ = refl
wildBiAdjoint-⊠ᶠ-⋔ᶠ .wildBiAdjoint.natR _ _ _ _ _ = refl
wildBiAdjoint-⊠ᶠ-⋔ᶠ .wildBiAdjoint.natPost _ _ _ _ _ = refl

areAdjointBiFunctors : (C : WildPreorder ℓ₁ ℓ₂)
  (f g : fst C → fst C → fst C) → Type (ℓ-max ℓ₁ ℓ₂)
areAdjointBiFunctors C f g =
  Σ[ l ∈ hasBiWPFunctorStructure C C C f ]
   Σ[ r ∈ hasBiWPFunctorStructure (C ^opʷᵖ) C C g ]
    (wildBiAdjoint C f g l r)

areAdjointBiFunctors-⊠ᶠ-⋔ᶠ :
  areAdjointBiFunctors ⌈ 𝑭𝑨𝑴 ℓ₁ ⌉ _⊠ᶠ_ _⋔ᶠ_
areAdjointBiFunctors-⊠ᶠ-⋔ᶠ .fst = hasBiWPFunctorStructure⊠ᶠ
areAdjointBiFunctors-⊠ᶠ-⋔ᶠ .snd .fst = hasBiWPFunctorStructure⋔ᶠ
areAdjointBiFunctors-⊠ᶠ-⋔ᶠ .snd .snd = wildBiAdjoint-⊠ᶠ-⋔ᶠ
