(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const n Int)

(declare-const b Int)
(declare-const a Int)
(declare-const t Int)
(declare-const d Int)

(assert (>= x 0))
(assert (>= y 0))
(assert (>= z 0))
(assert (>= n 0))

(assert (>= b 0))
(assert (>= a 0))
(assert (>= t 0))
(assert (>= d 0))

; rule getBaseReward(EffectiveBalance, TotalActiveBalance)
;   => EffectiveBalance *Int BASE_REWARD_FACTOR
;      /Int sqrtInt(TotalActiveBalance)
;      /Int BASE_REWARDS_PER_EPOCH
(define-fun getBaseReward ((b Int) (sqrt_t Int)) Int (div (div (* b 64) sqrt_t) 4))

(declare-const sqrt_t Int)
(assert (>= sqrt_t 0))

(push)
; rule getBaseReward(B, T) <=Int B => true requires B >=Int 0 andBool T >=Int 256
(assert (not (=>
    (and
        (>= (^ sqrt_t 2) 256)
    )
    (<= (getBaseReward b sqrt_t) b)
)))
(check-sat)
(pop)

(push)
; rule getBaseReward(B, T) >=Int 0 => true requires B >=Int 0 andBool T >=Int 1
(assert (not (=>
    (and
        (>= (^ sqrt_t 2) 1)
    )
    (>= (getBaseReward b sqrt_t) 0)
)))
(check-sat)
(pop)

; rule getMatchingReward(BaseReward, AttestingBalance, TotalActiveBalance)
;   => BaseReward *Int (AttestingBalance   /Int EFFECTIVE_BALANCE_INCREMENT)
;                 /Int (TotalActiveBalance /Int EFFECTIVE_BALANCE_INCREMENT)
(define-const c Int (^ 10 9))
(define-fun getMatchingReward ((b Int) (a Int) (t Int)) Int (div (* b (div a c)) (div t c)))

(push)
; rule getMatchingReward(B, A, T) <=Int B => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT andBool A <=Int T
(assert (not (=>
    (and
        (>= t c)
        (<= a t)
    )
    (<= (getMatchingReward b a t) b)
)))
(check-sat)
(pop)

(push)
; rule getMatchingReward(B, A, T) >=Int 0 => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT
(assert (not (=>
    (and
        (>= t c)
    )
    (>= (getMatchingReward b a t) 0)
)))
(check-sat)
(pop)

; rule getInclusionReward(BaseReward, InclusionDelay)
;   => (BaseReward -Int BaseReward /Int PROPOSER_REWARD_QUOTIENT) /Int InclusionDelay
(define-fun getInclusionReward ((b Int) (d Int)) Int (div (- b (div b 8)) d))

(push)
; rule getInclusionReward(B, D) <=Int B => true requires B >=Int 0 andBool D >=Int 1
(assert (not (=>
    (and
        (>= d 1)
    )
    (<= (getInclusionReward b d) b)
)))
(check-sat)
(pop)

(push)
; rule getInclusionReward(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 1
(assert (not (=>
    (and
        (>= d 1)
    )
    (>= (getInclusionReward b d) 0)
)))
(check-sat)
(pop)

; rule getInactivityPenalty(EffectiveBalance, FinalityDelay)
;   => EffectiveBalance *Int FinalityDelay /Int INACTIVITY_PENALTY_QUOTIENT
(define-fun getInactivityPenalty ((b Int) (d Int)) Int (div (* b d) (^ 2 25)))

(push)
; rule getInactivityPenalty(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 0
(assert (not (=>
    (and
        true
    )
    (>= (getInactivityPenalty b d) 0)
)))
(check-sat)
(pop)
