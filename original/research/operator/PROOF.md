# A direct operator proof of the type B cone conjecture

This argument proves the stronger rowwise interlacing assertion. All claims below
are derived here; the numerical checks in `check_operator.py` are supplementary.

## 1. Cayley operator

Put x=(z-1)/(z+1), C_n(z)=(z+1)^n B_n(x), and

    T f = 2(z^2-1) f' + 2z f.

Direct substitution in the defining type B recurrence gives C_0=1 and
C_{n+1}=T C_n. For 0<=k<=n,

    beta(n,k)(z)=(z+1)^n b(n,k)(x)
                 =sum_{j=0}^k binom(k,j)(z+1)^j C_{n-j}(z).          (1)

Every beta has degree n and positive leading coefficient, since each summand
has degree n and positive leading coefficient.

## 2. Root preservation on (-1,1)

If f has degree d, positive leading coefficient, and d simple roots in (-1,1),
then (T+c)f has d+1 simple roots in (-1,1), strictly interlacing those of f,
for every real -2<c<2.

Indeed, at a root r of f its value is 2(r^2-1)f'(r), the opposite sign of
f'(r). At the endpoints its values are (c-2)f(-1) and (c+2)f(1).
These signs give one zero in each of the d+1 intervals cut out by the roots
of f and the endpoints -1,1. Its degree is d+1 and its leading coefficient
is 2(d+1) times that of f. This also proves that each root is simple.

## 3. Independently varying operator parameters

For c=(c_1,...,c_n) in (-2,2)^n define

    F_n(z;c) = product_{i=1}^n (T+c_i) 1.

The operators commute, because each is T plus a constant. Section 2 therefore
implies that F_n has n simple roots in (-1,1), written increasingly
lambda_1(c)<...<lambda_n(c). Its derivative in c_j is

    G_j = product_{i != j}(T+c_i)1.

Since F_n=(T+c_j)G_j, the polynomial G_j strictly interlaces F_n. Positive
leading coefficients give G_j(lambda_i)/F_n'(lambda_i)>0. Differentiating
the simple-root equation gives

    partial lambda_i / partial c_j
       = -G_j(lambda_i)/F_n'(lambda_i) < 0.                         (2)

Thus every ordered root strictly decreases when any one constant parameter
increases. The roots extend continuously to the closed parameter cube.

## 4. Two endpoint polynomials have a common interior factor

Let P_n(z;a)=(T+a)^n1. For n>=1,

    P_n(z;2)  = (z+1) R_{n-1}(z),
    P_n(z;-2) = (z-1) R_{n-1}(z),                                 (3)

where R_0=2 and

    R_m=2(z^2-1)R_{m-1}'+4z R_{m-1}.

This follows by applying T+2 to (z+1)R and T-2 to (z-1)R: both produce the
same new interior factor. The same sign argument as in Section 2, with
endpoint multipliers -4 and 4, shows R_{n-1} has n-1 simple roots in (-1,1).

Write u_1<...<u_n for the roots of P_n(z;2), so u_1=-1. Equation (3) says
the roots of P_n(z;-2) are u_2,...,u_n,1. Let r_1<...<r_n be the roots of
C_n=P_n(z;0). By strict parameter monotonicity (2),

    u_i < r_i < u_{i+1}  (1<=i<n),    u_n<r_n<1.                   (4)

For any c in [0,2)^n with at least one positive coordinate, comparison
with the all-zero and all-two parameter vectors gives

    u_i < lambda_i(c) < r_i.                                      (5)

The lower inequality is strict: first increase every coordinate a small
positive amount while keeping them below 2, then take the monotone limit
to the all-two vector. The upper inequality is strict by increasing one
of the positive coordinates from zero (and monotonicity for the rest).

## 5. Substitute a=z+1 only after establishing constant-parameter facts

Let

    F_{n,k}(z;a)=T^(n-k)(T+a)^k1
                =sum_{j=0}^k binom(k,j)a^j C_{n-j}(z).

For a in (0,2), write its ordered roots as lambda_{i,k}(a). For k=0 these
are constant r_i. For k>=1, Section 3 shows they strictly decrease with a.
For every fixed a in (0,2), they strictly decrease when k increases:

    lambda_{i,k+1}(a) < lambda_{i,k}(a).                           (6)

Equation (1) gives beta(n,k)(z)=F_{n,k}(z;z+1). Its zeros in (-1,1)
are the solutions of

    z = lambda_{i,k}(z+1).                                        (7)

The left side minus the right side is strictly increasing. For k>=1,
it is negative at u_i (at i=1 use the continuous endpoint value a=0)
and positive at r_i, by (5). Consequently there is exactly one solution
s_{i,k} in (u_i,r_i), for each i. These are all n zeros of beta(n,k).
For k=0, set s_{i,0}=r_i.

Equation (6), evaluated pointwise before solving (7), implies

    s_{i,k+1}<s_{i,k}.                                            (8)

Indeed the increasing function z-lambda_{i,k+1}(z+1) is positive at the
zero of z-lambda_{i,k}(z+1), so its own zero lies to the left.

For k>ell, (4), (5), and (8) now yield, for i<n,

    s_{i,k} < s_{i,ell} <= r_i < u_{i+1} < s_{i+1,k}.
Thus beta(n,k) strictly interlaces beta(n,ell), with beta(n,ell) having the
larger roots. The Cayley map is increasing from (-1,1) onto (-infinity,0),
so the same is true of b(n,k) and b(n,ell).

Hence, for every n>=1,

    (b(n,n), b(n,n-1), ..., b(n,0))

is a strictly interlacing sequence of degree-n polynomials with negative
roots.

## 6. The full nonnegative cone

This can be concluded without invoking an external interlacing theorem.
At r_i, beta(n,k)(r_i) has sign (-1)^(n-i) for every k>=1, while
beta(n,0)(r_i)=0. Also beta(n,k)(-1)=C_n(-1)=(-2)^n for every k.

For a nonzero vector c_0,...,c_n>=0, if some c_k>0 with k>=1, the sum
sum_k c_k beta(n,k) has alternating nonzero signs at

    -1, r_1, ..., r_n.

It therefore has n distinct roots in (-1,1), one in each successive
interval. Its degree is exactly n. If only c_0 is positive, the sum is a
positive multiple of C_n and has the same conclusion. Applying the Cayley
map proves the exact requested conjecture, with the stronger conclusion
that every nonzero combination has n distinct strictly negative roots.

For n=0 the output is a nonnegative constant; the zero input is handled
by the usual convention that the zero polynomial is real-rooted.

## Scope

This proves the type B Eulerian transformation target. It does not itself
prove the analogous type B derangement transformation statement. No
novelty, independent review, or formal-verification claim is made here.
