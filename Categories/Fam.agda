{-# OPTIONS --cubical --guardedness --lossy-unification #-}
{-
This file constructs Fam as a wild category (𝑭𝑨𝑴). It also proves
J/univalence for this category.
-}
module Categories.Fam where

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
    ℓ₁ ℓ₂ ℓ₃ : Level

-- The type of families (indexed version of wild arrow category over
-- the universe)
Fam : (ℓ : Level) → Type (ℓ-suc ℓ)
Fam ℓ = Σ[ B ∈ Type ℓ ] (B → Type ℓ)

-- Hom types
Fam[_,_] : (D : Fam ℓ₁) (E : Fam ℓ₂)
  → Type _
Fam[_,_] (B , P) (Y , Q) = Σ[ f ∈ (B → Y) ] ((b : B) → P b → Q (f b))


-- Composition
compHomFam : (C : Fam ℓ₁) (D : Fam ℓ₂)
  (E : Fam ℓ₃) → Fam[ C , D ] → Fam[ D , E ]
  → Fam[ C , E ]
compHomFam _ _ _ (f , F) (g , G) .fst = g ∘ f
compHomFam _ _ _ (f , F) (g , G) .snd b x = G (f b) (F b x)

-- Identity
idHomFam : {C : Fam ℓ₁} → Fam[ C , C ]
idHomFam .fst x = x
idHomFam .snd x a = a

-- The category
𝑭𝑨𝑴 : (ℓ : Level) → WildCat (ℓ-suc ℓ) ℓ
𝑭𝑨𝑴 ℓ .ob = Fam ℓ
𝑭𝑨𝑴 ℓ .Hom[_,_] A B = Fam[_,_] A B
𝑭𝑨𝑴 ℓ .WildCat.id = idHomFam
𝑭𝑨𝑴 ℓ .cC {x = x} {y} {z} = compHomFam x y z
𝑭𝑨𝑴 ℓ .⋆IdL f = refl
𝑭𝑨𝑴 ℓ .⋆IdR f = refl
𝑭𝑨𝑴 ℓ .⋆Assoc f g h = refl

-------- Univalence and J --------

-- Equivalence of objects
_≃Fam_ : {ℓ₁ ℓ₂ : Level} → Fam ℓ₁ → Fam ℓ₂ → Type _
(A , B) ≃Fam (X , Y) = Σ[ e ∈ A ≃ X ] ((a : A) → B a ≃ Y (fst e a))

-- Identity equivalence
IdFamEquiv : {ℓ₁ : Level} (A : Fam ℓ₁) → A ≃Fam A
IdFamEquiv A .fst = idEquiv _
IdFamEquiv A .snd _ = idEquiv _

-- Total space of ≃Fam is contractible
isContrTot≃Fam : (A : Fam ℓ₁) → isContr (Σ[ B ∈ Fam ℓ₁ ] (A ≃Fam B))
isContrTot≃Fam A .fst = A , IdFamEquiv A
isContrTot≃Fam A .snd = lem _
  where
  aa = Σ-Π-Iso
  lem : isProp ((Σ[ B ∈ Fam _ ] (A ≃Fam B)))
  lem = isOfHLevelRetractFromIso 1
         (compIso Σ-assoc-Iso
           (compIso (Σ-cong-iso-snd (λ A
            → compIso (invIso Σ-assoc-Iso)
                (compIso (invIso (Σ-cong-iso-fst Σ-swap-Iso))
                  Σ-assoc-Iso)))
                  (compIso (invIso Σ-assoc-Iso)
                   (compIso (Σ-contractFstIso (isContrTot≃ (A .fst)))
                    (invIso (Σ-Π-Iso {B = λ _ → Type _}
                     {C = λ t B → A .snd t ≃ B}))))))
         (isPropΠ λ t → isContr→isProp (isContrTot≃ (A .snd t)))

-- J rule
JFam : {A : Fam ℓ₁} (P : (A' : Fam ℓ₁) → A ≃Fam A' → Type ℓ₂)
                    (e : P A (IdFamEquiv A))
                    (A' : _) (e : _) → P A' e
JFam {A = A} P idp A' e' =
  subst (λ x → P (fst x) (snd x))
    (isContrTot≃Fam A .snd (A' , e')) idp

-- Univalence
univalenceFam : ∀ {A B : Fam ℓ₁} → (A ≡ B) ≃ (A ≃Fam B)
univalenceFam =
  fundamentalTheoremOfId _≃Fam_ IdFamEquiv isContrTot≃Fam _ _

-- Univalence: β rule
univalenceFamRefl : {A : Fam ℓ₁}
  → fst (univalenceFam {A = A}) refl ≡ IdFamEquiv A
univalenceFamRefl = fundamentalTheoremOfIdβ _≃Fam_ IdFamEquiv isContrTot≃Fam _

-- Univalence: β rule, other way around
univalence⁻IdFamEquiv : {A : Fam ℓ₁}
  → invEq (univalenceFam {A = A}) (IdFamEquiv A) ≡ refl
univalence⁻IdFamEquiv {A = A} =
  cong (invEq univalenceFam) (sym (univalenceFamRefl {A = A}))
  ∙ retEq univalenceFam refl
