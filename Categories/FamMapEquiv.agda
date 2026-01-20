{-# OPTIONS --cubical --guardedness --lossy-unification #-}
{-
Equivalence between fam and map as (proto)-wild categories
-}
module Categories.FamMapEquiv where

-- Local imports
open import Prelude
open import Categories.ProtoWildCat
open import Categories.Map
open import Categories.Fam

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

open WildCat
open WildFunctor
open Iso

-- We are sticking to one universe here, mainly for the sake of
-- readability (full generality will make Agda struggle with inferring
-- implicit arguments)
private
  variable
    ℓ : Level

-- Construction of functor 𝑴𝑨𝑷 → 𝑭𝑨𝑴
Map→Fam : Map ℓ → Fam ℓ
Map→Fam (A , B , f) .fst = B
Map→Fam (A , B , f) .snd b = fiber f b

Map→Fam⃗ : {x y : _} → 𝑴𝑨𝑷 ℓ [ x , y ]
                      → 𝑭𝑨𝑴 ℓ [ Map→Fam x , Map→Fam y ]
Map→Fam⃗ (α , β , q) .fst = β
Map→Fam⃗ (α , β , q) .snd b (a , fp) .fst = α a
Map→Fam⃗ (α , β , q) .snd b (a , fp) .snd =
  sym (q a) ∙ cong β fp

Map→Fam⃗Id : {x : Map ℓ} → Map→Fam⃗ {x = x} idHomMap ≡ idHomFam
Map→Fam⃗Id =
  ΣPathP (refl , funExt λ t → funExt λ {(a , fp)
    → ΣPathP (refl , (sym (lUnit fp)))})

Map→Fam⃗Comp : {x y z : Map ℓ}
  (f : 𝑴𝑨𝑷 ℓ [ x , y ]) (g : 𝑴𝑨𝑷 ℓ [ y , z ])
    → Map→Fam⃗ (compHomMap x y z f g)
     ≡ compHomFam (Map→Fam x) (Map→Fam y) (Map→Fam z)
                  (Map→Fam⃗ f)
                  (Map→Fam⃗ g)
Map→Fam⃗Comp (α , β , q) (γ , ε , r) =
  ΣPathP (refl , funExt λ b → funExt λ {(x , fp)
    → ΣPathP (refl , cong₂ _∙_ (symDistr _ _) refl
                   ∙ sym (assoc _ _ _)
                   ∙ cong₂ _∙_ refl (sym (cong-∙ ε _ _)))})

Map⇒Fam : WildFunctor (𝑴𝑨𝑷 ℓ) (𝑭𝑨𝑴 ℓ)
Map⇒Fam .F-ob = Map→Fam
Map⇒Fam .F-hom = Map→Fam⃗
Map⇒Fam .F-id = Map→Fam⃗Id
Map⇒Fam .F-seq = Map→Fam⃗Comp

-- Construction of functor 𝑴𝑨𝑷 → 𝑭𝑨𝑴
Fam→Map : Fam ℓ → Map ℓ
Fam→Map (A , B) .fst = Σ A B
Fam→Map (A , B) .snd .fst = A
Fam→Map (A , B) .snd .snd = fst

Fam→Map⃗ : {x y : ob (𝑭𝑨𝑴 _)}
         → 𝑭𝑨𝑴 ℓ [ x , y ]
         → 𝑴𝑨𝑷 ℓ [ Fam→Map x , Fam→Map y ]
Fam→Map⃗ F .fst (a , b) .fst = fst F a
Fam→Map⃗ F .fst (a , b) .snd = snd F a b
Fam→Map⃗ (f , g) .snd .fst = f
Fam→Map⃗ F .snd .snd _ = refl

Fam→Map⃗Id : (x : Fam ℓ) → Fam→Map⃗ (idHomFam {C = x}) ≡ idHomMap
Fam→Map⃗Id x = refl

Fam→Map⃗Comp : {x y z : Fam ℓ} (f : Fam[ x , y ]) (g : Fam[ y , z ])
  → Fam→Map⃗ (compHomFam x y z f g)
   ≡ compHomMap (Fam→Map x) (Fam→Map y) (Fam→Map z)
                (Fam→Map⃗ {x = x} {y} f) (Fam→Map⃗ {x = y} {z} g)
Fam→Map⃗Comp f g = ΣPathP (refl , (ΣPathP (refl , funExt λ x → rUnit refl)))

Fam⇒Map : WildFunctor (𝑭𝑨𝑴 ℓ) (𝑴𝑨𝑷 ℓ)
Fam⇒Map .F-ob = Fam→Map
Fam⇒Map .F-hom = Fam→Map⃗
Fam⇒Map .F-id = refl
Fam⇒Map .F-seq f g = Fam→Map⃗Comp f g

-- Cancellation of functors (on objects)
Fam→Map→Fam : (A : Fam ℓ) →  Map→Fam (Fam→Map A) ≃Fam A
Fam→Map→Fam (A , B) .fst = idEquiv A
Fam→Map→Fam (A , B) .snd a = isoToEquiv (Iso-fibFst-fib a)

Map→Fam→Map : (A : Map ℓ) → Fam→Map (Map→Fam A) ≃Map A
Map→Fam→Map (A , B , f) .fst =
  isoToEquiv (compIso (invIso Σ-assoc-Iso)
    (compIso (Σ-cong-iso-fst Σ-swap-Iso)
     (compIso Σ-assoc-Iso
      (compIso (Σ-cong-iso-snd
       (λ a → isContr→Iso (isContrSingl _) isContrUnit))
       rUnit×Iso))))
Map→Fam→Map (A , B , f) .snd .fst = idEquiv B
Map→Fam→Map (A , B , f) .snd .snd (a , b , p) = sym p

Iso-Fam-Map : Iso (Fam ℓ) (Map ℓ)
Iso-Fam-Map .fun = Fam→Map
Iso-Fam-Map .inv = Map→Fam
Iso-Fam-Map .sec A = invEq univalenceMap (Map→Fam→Map _)
Iso-Fam-Map .ret A = invEq univalenceFam (Fam→Map→Fam _)

-- Cancellation of functors (on homs)
Iso⃗Map-Fam : {A B : Fam ℓ} → Iso Fam[ A , B ] Map[ Fam→Map A , Fam→Map B ]
Iso⃗Map-Fam .fun = Fam→Map⃗
Iso⃗Map-Fam {B = B} .inv (F , G , T) =
  G , λ b a → subst (B .snd) (sym (T (b , a))) (F (b , a) .snd)
Iso⃗Map-Fam {B = B} .sec (F , G , T) =
  ΣPathP ((funExt λ x
  → ΣPathP (T x , λ j → transp (λ i → snd B (T x (~ i ∨ j))) j (F x .snd)))
    , ΣPathP (refl , funExt λ {(a , p) i j → T (a , p) (i ∧ j)}))
Iso⃗Map-Fam .ret _ =
  ΣPathP (refl , (funExt (λ _ → funExt (λ _ → transportRefl _)) ))

-- The main result
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 : ⌈ 𝑭𝑨𝑴 ℓ ⌉ ≅ᴾᵂ ⌈ 𝑴𝑨𝑷 ℓ ⌉
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 .fst .fst = Fam→Map
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 .fst .snd .fst  = Fam→Map⃗
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 .fst .snd .snd .fst _ = Fam→Map⃗Id _
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 .fst .snd .snd .snd = Fam→Map⃗Comp
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 .snd .fst = isoToIsEquiv Iso-Fam-Map
𝑭𝑨𝑴≅ᴾᵂ𝑴𝑨𝑷 .snd .snd x y = isoToIsEquiv Iso⃗Map-Fam
