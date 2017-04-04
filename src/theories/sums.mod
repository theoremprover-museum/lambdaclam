
module sums.

accumulate analytica.


%% Theorem 1 taken from Toby Walsh's Maple + LClam-Lite paper
%%
%%@InProceedings{TobyMaple,
%%  author =       {T. Walsh},
%% title =        {{P}roof {P}lanning in {M}aple},
%%  booktitle =    {Proc. of the CADE-17 workshop on Automated Deduction in the Context of Mathematics},
%%  year =         2000
%%}
%%================================================
%% forall n.
%%        n
%%      -----
%%      \                   2
%%       )   i = 1/2 (n + 1)  - 1/2 n - 1/2
%%      /
%%      -----
%%      i = 0
%%
%% Note:   1/2*(n*(n+1)) on the right hand side does not work! 
%% Reason (Maple):
%% > simplify(1/2*(n*(n+1)));
%%                                      1/2 n (n + 1)
%% but 
%% > sum(i, i=0..n);
%%                                          2
%%                               1/2 (n + 1)  - 1/2 n - 1/2

top_goal sums sum_i []
        (app forall (tuple [nat, 
        (abs n\ 
         (app eq 
         (tuple [(app summation (tuple [zero, n, (abs x\ x)])),
                 (app minus 
                     (tuple [(app minus 
                                 (tuple [
                                   (app otimes
                                       (tuple [onehalf, 
                                              (app exp (tuple [(app plus  (tuple [n, (app s zero)])),
                                                               (app s (app s zero))
                                                           ]))])),
                                   (app otimes (tuple [onehalf, n]))])),
                             onehalf]))
                 ])))])).


%% Theorem 2 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n.
%%        n
%%      -----        3     2
%%      \     2    2n  + 3n  + n        
%%       )   i  = ----------------
%%      /                6
%%      -----
%%      i = 0
%%
%%
%%> simplify( (2*n^3+3*n^2+n)/6);
%%                                     3        2
%%                                1/3 n  + 1/2 n  + 1/6 n
%%
%%> sum(i^2, i=0..n);
%%                                  3              2
%%                       1/3 (n + 1)  - 1/2 (n + 1)  + 1/6 n + 1/6


top_goal sums sum_i_square []
        (app forall (tuple [nat, 
        (abs n\ 
         (app eq 
         (tuple [(app summation (tuple [zero, n, (abs x\ (app otimes (tuple [x,x])))])),
                 (app plus 
                     (tuple [(app minus 
                                 (tuple [
                                   (app otimes
                                       (tuple [(app odiv (tuple [one, three])),  % 1/3
                                               (app exp (tuple [(app plus  (tuple [n, (app s zero)])),
                                                                (app s (app s (app s zero)))]))])),
                                   (app otimes
                                       (tuple [onehalf,  % 1/2
                                               (app exp (tuple [(app plus  (tuple [n, (app s zero)])),
                                                                (app s (app s zero))]))]))
                                  ])),
                             (app plus 
                                 (tuple [(app otimes (tuple [(app odiv (tuple [one, six])), n])),
                                         (app odiv (tuple [one, six]))]))
                            ]))])))])).


%% Theorem 3 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n.
%%        n
%%      -----                            3
%%      \        2                  (n+1) - n - 1
%%       )   i+ i  = (1) + (2)  = -----------------
%%      /                                3
%%      -----
%%      i = 0
%%
%%> sum(i+i^2, i=0..n);
%%                                                        3
%%                             - 1/3 n - 1/3 + 1/3 (n + 1)
%%> simplify(sum(i+i^2, i=0..n));
%%                                               3    2
%%                                  2/3 n + 1/3 n  + n

%%> simplify(((n+1)^3 -n -1)/3);
%%                                               3    2
%%                                  2/3 n + 1/3 n  + n



top_goal sums sum_i_plus_i_square []
        (app forall (tuple [nat, 
        (abs n\ 
         (app eq 
         (tuple [(app summation (tuple [zero, n, (abs x\ (app plus (tuple [x, (app otimes (tuple [x,x]))])))])),
                 (app odiv 
                     (tuple [(app minus 
                                 (tuple [
                                    (app minus 
                                       (tuple [(app exp
                                               (tuple [(app s n), (app s (app s (app s zero)))])),
                                               n])),
                                               (app s zero)])),
                             (app s (app s (app s zero)))]))])))])).


%% Theorem 4 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n. a <> 1 =>
%%        n
%%      -----        n+1 
%%      \     i     a   - 1
%%       )   a  = ----------
%%      /            a-1 
%%      -----
%%      i = 0
%%

type a osyn.
has_otype sums a nat.

top_goal sums sum_a_to_i [(app neg (app eq (tuple [a, (app s zero)])))]
        (app forall (tuple [nat, 
        (abs n\ 
        (app eq 
         (tuple [(app summation (tuple [zero, n, (abs x\ (app exp (tuple [a,x])))])),
                 (app odiv 
                     (tuple [(app minus 
                                 (tuple [
                                    (app exp 
                                       (tuple [a,
                                               (app s n)])),
                                 (app s zero)])),
                             (app minus
                               (tuple [a, (app s zero)]))]))])))])).

%       4 & $\sum a^i  = \frac{a^{n+1} -1}{a-1}$


%% Theorem 5 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n. a <> 1 =>
%%        n
%%      -----         (n + 2)      (n + 1)    (n + 1)
%%      \       i   n*a       - n*a        - a        + a
%%       )   i*a  = ---------------------------------------
%%      /                                  2
%%      -----                       (a - 1) 
%%      i = 0
%%
%% Maple says:
%%> sum(i*a^i, i=0..n);
%%                       (n + 1)
%%                      a        ((n + 1) a - n - 1 - a)      a
%%                      -------------------------------- + --------
%%                                         2                      2
%%                                  (a - 1)                (a - 1)

%%> simplify(sum(i*a^i, i=0..n));
%%                         (n + 2)      (n + 1)      (n + 1)
%%                        a        n - a        n - a        + a
%%                        --------------------------------------
%%                                              2
%%                                       (a - 1)

%top_goal sums sum_i_times_a_to_i [(app neg (app eq (tuple [a, (app s zero)])))]
%        (app forall (tuple [nat, 
%        (abs n\ 
%        (app eq 
%         (tuple [(app summation (tuple [zero, n, (abs x\ (app otimes (tuple [x, (app exp (tuple [a,x]))])))])),
%                 (app odiv 
%                     (tuple [(app plus 
%                               (tuple [(app minus 
%                                        (tuple [
%                                         (app minus 
%                                          (tuple [(app otimes 
%                                                  (tuple [n, (app exp (tuple [a, (app s (app s n))]))])),
%                                                  (app otimes 
%                                                  (tuple [n, (app exp (tuple [a, (app s n)]))]))])),
%                                       (app exp (tuple [a, (app s n)]))])),
%                                    a])),
%                            (app exp (tuple [(app minus (tuple [a, (app s zero)])), (app s (app s zero))]))
%                        ]))])))])).


%        5 & $\sum ia^i  = \frac{(n+1)a^{n+1}-a\cdot\frac{a^{n+1}-1}{a-1}}{a-1}$


%% Theorem 6 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n. a <> 1 =>
%%        n
%%      -----                  (n + 1)    (n + 1)    
%%      \           i   (n+1)*a          a        -  1
%%       )   (i+1)*a  = -----------  -  ---------------------------
%%      /                (a - 1)                       2
%%      -----                                   (a - 1) 
%%      i = 0
%%
%% LateX:    6 & $\sum (i+1)\cdot a^i  = \frac{(n+1)a^{n+1}}{a-1}-\frac{a^{n+1}-1}{(a-1)^2}$
%% Maple says:
%%> simplify(sum((i+1)*a^i, i=0..n));
%%                      (n + 1)    (n + 2)      (n + 2)    (n + 1)
%%                   2 a        - a        n - a        + a        n - 1
%%                 - ---------------------------------------------------
%%                                               2
%%                                        (a - 1)
%%> simplify(((n+1)*a^(n+1))/(a-1) - (a^(n+1)-1)/((a-1)^2));
%%                      (n + 1)    (n + 2)      (n + 2)    (n + 1)
%%                   2 a        - a        n - a        + a        n - 1
%%                 - ---------------------------------------------------
%%                                               2
%%                                        (a - 1)

%top_goal sums sum_s_i_times_a_to_i [(app neg (app eq (tuple [a, (app s zero)])))]
%        (app forall (tuple [nat, 
%        (abs n\ 
%        (app eq 
%         (tuple [(app summation (tuple [zero, n, (abs x\ (app otimes (tuple [(app s x), (app exp (tuple [a,x]))])))])),
%                 (app minus 
%                  (tuple [(app odiv 
%                           (tuple [(app otimes (tuple [(app s n), (app exp (tuple [a, (app s n)]))])),
%                                   (app minus (tuple [a, (app s zero)]))])),
%                          (app odiv 
%                           (tuple [(app minus (tuple [(app exp (tuple [a, (app s n)])), (app s zero)])),
%                                   (app exp (tuple [(app minus (tuple [a, (app s zero)])), (app s (app s zero))]))]))
%                         ]))])))])).

%% Theorem 7 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n. a <> 1 =>
%%        n
%%      -----                
%%      \        1         n 
%%       )   -------- = -------
%%      /     i*(i+1)    (n+1) 
%%      -----                  
%%      i = 0
%%
%% LateX:   7 & $\sum \frac{1}{i(i+1)} = \frac{n}{n+1}$ 
%% Maple says:


%top_goal sums sum_1_div_i_times_s_i [(app neg (app eq (tuple [a, (app s zero)])))]
%        (app forall (tuple [nat, 
%        (abs n\ 
%        (app eq 
%         (tuple [(app summation (tuple [zero, n, (abs x\ (app odiv (tuple [(app s zero), (app otimes (tuple [x, (app s x)]))])))])),
%                 (app odiv (tuple [n, (app s n)]))])))])).


%% Theorem 8 taken from Toby Walsh's Maple + LClam-Lite paper
%%================================================
%% forall n.
%%        n
%%      -----
%%      \     
%%       )   Fib(i) = Fib(n+2) - 1
%%      /
%%      -----
%%      i = 0
%%
%%
%% Latex:    8 & $\sum Fib(i)  = Fib(n+2) - 1$
%% should not need any CAS simplification...


top_goal sums sum_fib []
        (app forall (tuple [nat, 
        (abs n\ 
         (app eq 
         (tuple [(app summation (tuple [zero, n, (abs x\ (app fibonacci x))])),
                 (app minus
                     (tuple [(app fibonacci (app s (app s n))),
                             (app s zero)]))])))])).


/*
summation in OpenMath
<OMOBJ>
        <OMA>
          <OMS cd="arith1" name="sum"/>
            <OMA>
              <OMS cd="interval1" name="integer_interval"/>
              <OMI> 1 </OMI>
              <OMI> 10 </OMI>
            </OMA>
          <OMBIND>
            <OMS cd="fns1" name="lambda"/>
              <OMBVAR>
                <OMV name="x"/>
              </OMBVAR>
              <OMA>
                <OMS cd="arith1" name="divide"/>
                <OMI> 1 </OMI>
                <OMV name="x"/>
              </OMA>
          </OMBIND>
        </OMA>
      </OMOBJ>
*/
end

