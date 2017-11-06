{-# OPTIONS --rewriting --without-K #-}

{-

To get Andrea Vezzosi's flat-ified Agda:

git clone https://github.com/agda/agda
cd agda
git checkout flat
cabal install --program-suffix=-flat

and then change your emacs startups to point to agda-flat and agda-mode-flat

-}

open import Agda.Primitive

module FlatSharp where

  -- library 

  data _==_ {l1 : Level} {A : Set l1} (a : A) : A → Set l1 where
    refl : a == a

  transport : ∀ {l1 l2 : Level} {A : Set l1} (C : A →  Set l2) {M N : A} (P : M == N) → C M → C N
  transport C refl x = x

  ap : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f refl = refl

  apc : ∀ {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} {B : Set l2} {M N :{♭} A}
       (f : (x :{♭} A) → B) → M == N → (f M) == (f N)
  apc f refl = refl

  -- ap2 :  {A B C : Set} {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  -- ap2 f refl refl = refl

  ! : {l1 : Level} {A : Set l1} {M N : A} → M == N → N == M
  ! refl = refl

  _∘_  : {l1 : Level} {A : Set l1} {M N P : A} → N == P → M == N → M == P
  β ∘ refl = β

  record Σe {l1 l2 : Level} (A : Set l1) (B : A -> Set l2) : Set (l1 ⊔ l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σe public

  Σ : {l1 l2 : Level} {A : Set l1} -> (B : A -> Set l2) -> Set (l1 ⊔ l2)
  Σ {_}{_}{A} B = Σe A B

  infixr 0 _,_

  -- ----------------------------------------------------------------------

  data ♭ {l :{♭} Level} (A :{♭} Set l) : Set l where
    ♭i : (a :{♭} A) → ♭ A

  counit : ∀ {l :{♭} _} {A :{♭} Set l} → ♭ A → A
  counit (♭i x) = x

  ♭elim : ∀ {c} {l :{♭} Level} {A :{♭} Set l}
         → (C : ♭ A → Set c)
         → ((u :{♭} A) → C (♭i u))
         → (x : ♭ A) → C x
  ♭elim C f (♭i x) = f x

  -- crisp flat induction and crisp id induction are provable by pattern matching

  ♭elim-crisp : ∀ {c} {l :{♭} Level} {A :{♭} Set l}
         → (C : (x :{♭} ♭ A) → Set c)
         → ((u :{♭} A) → C (♭i u))
         → (x :{♭} ♭ A) → C x
  ♭elim-crisp C f (♭i x) = f x

  ff1 : {l :{♭} Level} {A :{♭} Set l} → ♭ (♭ A) → ♭ A
  ff1 (♭i (♭i x)) = ♭i x

  ff2 : {l :{♭} Level} {A :{♭} Set l} → ♭ A → ♭ (♭ A) 
  ff2 (♭i x) = ♭i (♭i x)

  ff3 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ A) → ff1 (ff2 x) == x
  ff3 (♭i x) = refl

  ff4 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ (♭ A)) → ff2 (ff1 x) == x
  ff4 (♭i (♭i x)) = refl

  path-ind-crisp : ∀ {l :{♭} Level} {A :{♭} Set l} {a :{♭} A}
         → (C : (y :{♭} A) (p : a == y) → Set l)
         → C a refl
         → (y :{♭} A) (p :{♭} a == y) → C y p
  path-ind-crisp C b _ refl = b


  -- ----------------------------------------------------------------------
  -- sharp

  postulate
    Rewrite : {l1 : Level} {A : Set l1} → A → A → Set l1
  {-# BUILTIN REWRITE Rewrite #-}

  postulate
    -- postulate a predicate closed under Π, Id, and the universe of itself
    Codisc : {l : Level} (A : Set l) → Set l
    Codisc-prop : {l : Level} (A : Set l) (x y : Codisc A) → x == y
    Codisc-Π : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} → ((x : A) → Codisc (B x)) → Codisc ((x : A) → B x)
    Codisc-= : {l1 : Level} {A : Set l1} {a1 a2 : A} → Codisc A → Codisc (a1 == a2) 
    Codisc-Codisc : {l1 : Level} → Codisc (Σ \ (A : Set l1) → Codisc A)

    -- you can put something in the crisp context if the conclusion is codiscrete
    promote : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} 
              (C : A → Set l2) → 
              ((x : A) → Codisc (C x))
            → ((x :{♭} A) → (C x))
            → (x : A) → (C x)
    promoteβ : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} (C : A → Set l2) (cc : ((x : A) → Codisc (C x)))
            → (f : (x :{♭} A) → (C x))
            → (x :{♭} A) → (promote C cc f x) == (f x)
  -- FIXME: tried making this definitional, but it fires even when x isn't crisp
  -- {-# REWRITE promoteβ #-}

  -- judgemental version of ♭ (♯ A) ≅ ♭ A
  postulate
    ♯  : {l : Level} (A : Set l) → Set l
    Codisc-♯ : {l : Level} {A : Set l} → Codisc(♯ A)
    ♯i : {l : Level} {A : Set l} → A → ♯ A
    ♯e : {l :{♭} Level} {A :{♭} Set l} → (x :{♭} (♯ A)) → A
    ♯β : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → Rewrite (♯e (♯i x)) x
    ♯η-crisp : {l :{♭} Level} {A :{♭} Set l} (x :{♭} ♯ A) → x == ♯i (♯e x)
  {-# REWRITE ♯β #-}
  postulate
    -- coherence between β (which is a rewrite so definitional) and η
    ♯η-crisp-triangle : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → ♯η-crisp (♯i x) == refl

  -- postulates seem to be treated as "external" -- they can be substituted for crisp variables
  example : {A :{♭} Set} (a :{♭} A) → ♭(♯ A)
  example a = ♭i (♯i a)

  -- (correctly) doesn't work: 
  -- example' : {A :{♭} Set} (a :{♭} A) → (♯i' : A → ♯ A) → ♭(♯ A)
  -- example' a ♯i' = ♭i (♯i' a)

  -- from these we can prove the modality elim for ♯

  transport-♯ : {l :{♭} Level} {A :{♭} Set l} {A' : Set l} → (p : A == A') → 
              {x :{♭} (♯ A)} → transport ♯ p x == ♯i (transport (\ X → X) p (♯e x))
  transport-♯ refl = ♯η-crisp _

  abstract
    ♯-elim : {l1 l2 : Level} {A : Set l1} (C : ♯ A → Set l2) (cc : (x : ♯ A) → Codisc (C x))
           → ((x : A) → C (♯i x))
           → ((x : ♯ A) → C x)
    ♯-elim {A = A} C cc f x = 
      promote (λ X → (x : ♯ X) → (p : X == A) → C (transport (\ Y → ♯ Y) p x)) 
              (\ _ → Codisc-Π (\ _ → Codisc-Π (\ _ → cc _)))
              (\ A' → promote _ (\ _ → Codisc-Π (\ _ → cc _)) (\ x → \ p → transport C (! (transport-♯ p)) (f (transport (\ X → X) p (♯e x)))))
              A x refl 

    ♯-elim-β : {l1 l2 : Level} {A : Set l1} (C : ♯ A → Set l2) (cc : (x : ♯ A) → Codisc (C x))
             → (f : (x : A) → C (♯i x))
             → (x : A) 
             → ♯-elim C cc f (♯i x) == f x
    ♯-elim-β {A = A} C cc f x =  
      promote (\ X → (x : X) (p : X == A) → ♯-elim C cc f (♯i (transport (\ Y → Y) p x)) == f ((transport (\ Y → Y) p x))) (\ _ → Codisc-Π (\ _ → Codisc-Π (\ _ → Codisc-= (cc _)))) 
      (\ X → promote _ (\ _ → Codisc-Π (\ _ → Codisc-= (cc _))) 
              (\ z → \ {refl → 
                 ( ap (\ p → transport C (! p) (f z)) (♯η-crisp-triangle z) ∘ 
                  ap (\ h → h refl) (promoteβ (λ z₁ → (x₁ : X == X) → C (transport ♯ x₁ z₁)) (λ z₁ → Codisc-Π (λ z₂ → cc (transport ♯ z₂ z₁))) (λ x₁ p → transport C (! (transport-♯ p)) (f (transport (λ X₁ → X₁) p (♯e x₁)))) (♯i z))) ∘ -- possibly dubious refl match, but seemed to work OK
                  ap (\ h → h (♯i z) refl) (promoteβ (λ X₁ → (x₁ : ♯ X₁) (p : X₁ == X) → C (transport ♯ p x₁)) (λ z₁ → Codisc-Π (λ z₂ → Codisc-Π (λ z₃ → cc (transport ♯ z₃ z₂)))) (λ A' → promote (λ z₁ → (x₁ : A' == X) → C (transport ♯ x₁ z₁)) (λ z₁ → Codisc-Π (λ z₂ → cc (transport ♯ z₂ z₁))) (λ x₁ p → transport C (! (transport-♯ p)) (f (transport (λ X₁ → X₁) p (♯e x₁))))) X)})) 
      A x refl 

    ♯-rec : {l1 l2 : Level} {A : Set l1} {C : Set l2} (cc : Codisc C)
           → (A → C)
           → (♯ A → C)
    ♯-rec cc f x = ♯-elim _ (\ _ -> cc) f x

    ♯-rec-crisp-β : {l1 l2 :{♭} Level} {A :{♭} Set l1} {C : Set l2} (cc : Codisc C)
                   → (f : A → C) (x :{♭} ♯ A)
                   → ♯-rec cc f x == f (♯e x)
    ♯-rec-crisp-β cc f x = ♯-elim-β _ (\ _ → cc) f (♯e x) ∘ ap (♯-rec cc f) (♯η-crisp x) 

  -- ♭ (♯ A) ≅ ♭ A

  fs1 : {l :{♭} Level} {A :{♭} Set l} → ♭ (♯ A) → ♭ A
  fs1 = ♭elim _ (\ u → ♭i (♯e u))

  fs2 : {l :{♭} Level} {A :{♭} Set l} → ♭ A → ♭ (♯ A) 
  fs2 (♭i x) = ♭i (♯i x)

  fs3 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ A) → fs1 (fs2 x) == x
  fs3 (♭i x) = refl

  fs4 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ (♯ A)) → fs2 (fs1 x) == x
  fs4 (♭i x) = apc ♭i (! ( (♯η-crisp x) ))

  -- ♯ (♯ A) ≅ ♯ A follows from the elim
  
  -- ♯ (♭ A) ≅ ♯ A 

  sf1 : {l :{♭} Level} {A :{♭} Set l} → ♯ (♭ A) → ♯ A
  sf1 = ♯-elim _ (λ _ → Codisc-♯) (\x → ♯i (counit x))

  sf2 : {l :{♭} Level} {A :{♭} Set l} → ♯ A → ♯ (♭ A) 
  sf2 = ♯-elim _ (\ _ → Codisc-♯) (promote _ (\ _ → Codisc-♯) (\ x → ♯i (♭i x)))

  sf3 : {l :{♭} Level} {A :{♭} Set l} → (x : ♯ A) → sf1 (sf2 x) == x
  sf3 {A = A} = ♯-elim _ (\ _ → Codisc-= (Codisc-♯)) (promote _ (\ _ → Codisc-= (Codisc-♯)) 
                (\ x → (♯-elim-β (\ _ → ♯ A)(λ _ → Codisc-♯) (\x → ♯i (counit x)) (♭i x)  ∘ 
                         (ap (♯-elim (λ _ → ♯ A) (λ _ → Codisc-♯) (λ x₁ → ♯i (counit x₁))) 
                             (promoteβ (λ _ → ♯ (♭ A)) (λ _ → Codisc-♯) (λ x₁ → ♯i (♭i x₁)) x) 
                          ∘ ap sf1 (♯-elim-β _ (\ _ → Codisc-♯) (promote _ (\ _ → Codisc-♯) (\ x → ♯i (♭i x))) x)) 
                         )) )

  sf4 : {l :{♭} Level} {A :{♭} Set l} → (x : ♯ (♭ A)) → sf2 (sf1 x) == x
  sf4 = ♯-elim _ (\ _ → Codisc-= (Codisc-♯)) (promote _ (\ _ → Codisc-= (Codisc-♯)) (♭elim-crisp _ {!similar!}) )

  -- some things that would use the ♯ formation rule promotion

  Codiscs : {l : Level} → Set (lsuc l)
  Codiscs = Σ Codisc

  Σ-interact-crisp1 : {A :{♭} Set} {B :{♭} A → Set} → ♯(Σ B) → 
               Σ \ (x : ♯ A) → fst (promote (\ _ → Codiscs) (\ _ → Codisc-Codisc) (\ x → (♯ (B (♯e x))) , Codisc-♯) x)
  Σ-interact-crisp1 {A = A} {B = B} p = 
     ♯-rec Codisc-♯ (\ p' → ♯i (fst p')) p , 
     promote 
     (\ q → fst (promote (λ _ → Codiscs) (λ _ → Codisc-Codisc) (λ x → ♯ (B (♯e x)) , Codisc-♯) (♯-rec Codisc-♯ (\ p' → ♯i (fst p')) q))) 
     (\ q → snd (promote (λ _ → Codiscs) (λ _ → Codisc-Codisc) (λ x → ♯ (B (♯e x)) , Codisc-♯) (♯-rec Codisc-♯ (\ p' → ♯i (fst p')) q))) 
     (\ q → transport fst (! (promoteβ (λ _ → Codiscs) (λ _ → Codisc-Codisc) (λ x → ♯ (B (♯e x)) , Codisc-♯) (♯-rec Codisc-♯ (\ p' → ♯i (fst p')) q))) (transport (\ h → ♯ (B h)) (apc ♯e (! (♯-rec-crisp-β Codisc-♯ (λ p' → ♯i (fst p')) q)) ) (♯i (snd (♯e q))))) p

  escape : ♯ Set → Set
  escape A = fst (promote (\ _ → Codiscs) (λ _ → Codisc-Codisc) (\ X → ♯ (♯e X) , Codisc-♯) A)

  escape-♯i-crisp : (A :{♭} Set) → escape (♯i A) == ♯ A
  escape-♯i-crisp X = ap fst (promoteβ (λ _ → Σe Set Codisc) (λ _ → Codisc-Codisc) (λ X₁ → ♯ (♯e X₁) , Codisc-♯) (♯i X))
  
  escape-♯i-1 : (A : Set) → escape (♯i A) → ♯ A
  escape-♯i-1 A = 
    promote (\ X → escape (♯i X) -> ♯ X) (\ _ → Codisc-Π (\ _ → Codisc-♯)) 
            (\ X → transport (\ X → X) (escape-♯i-crisp X))
            A 

  escape-♯i-2 : (A : Set) → ♯ A → escape (♯i A) 
  escape-♯i-2 A = 
    promote (\ X → ♯ X -> escape (♯i X)) 
            (\ _ → Codisc-Π (\ _ → snd (promote (\ _ → Codiscs) (λ _ → Codisc-Codisc) (\ X → ♯ (♯e X) , Codisc-♯) _))) 
            (\ X → transport (\ X → X) (! (escape-♯i-crisp X)))
            A 
