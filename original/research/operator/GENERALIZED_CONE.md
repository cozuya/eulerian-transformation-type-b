# A larger cone and both transformations

This is an extension of Sections 1–4 of `PROOF.md`. It proves both requested
transformation statements by the same self-contained operator argument.

Define

    K_n = { sum_{j=0}^n d_j (t-1)^(n-j)(t+1)^j : d_j>=0 }.

For every nonzero p in K_n, B[p] has n distinct real roots, all nonpositive.
They are all strictly negative if p(1)>0; when p(1)=0, exactly one is zero.

## Proof

Use T, C_n, F_n(z;c), P_n(z;a), and R_{n-1} as defined and proved in
Sections 1–4 of `PROOF.md`. Let the roots of R_{n-1} be

    -1=v_0 < v_1 < ... < v_{n-1} < v_n=1.

The endpoint identities

    P_n(z;2)=(z+1)R_{n-1}(z),
    P_n(z;-2)=(z-1)R_{n-1}(z)

and coordinatewise strict root monotonicity imply the following uniform
bound: for any fixed c in (-2,2)^n, F_n(z;c) has exactly one simple root
in each interval (v_{i-1},v_i), i=1,...,n.

Indeed, its i-th ordered root is strictly between the i-th roots of the
all-two and all-minus-two endpoint polynomials, which are v_{i-1} and v_i.
Thus, at v_i for 1<=i<n,

    sign F_n(v_i;c)=(-1)^(n-i),                                    (1)

independently of the choice of c in the open cube.

For a basis polynomial p_j(t)=(t-1)^(n-j)(t+1)^j, put

    H_j(z)=(z+1)^n B[p_j]((z-1)/(z+1)).

Expanding p_j, and using C_m=T^m1, shows that H_j(z) is obtained by
first forming F_n(z;c) with n-j parameters equal to -(z+1) and j
parameters equal to +(z+1). This statement means substitution AFTER
the product of constant-parameter operators has been evaluated.

For z=v_i in (-1,1), all substituted constants are in (-2,2), so (1)
gives sign H_j(v_i)=(-1)^(n-i), for every j. Therefore every nonzero
nonnegative sum H=sum_j d_j H_j has the same strict signs at all v_i.

The polynomial H has degree at most n. Its endpoint values are

    H(-1)=(-2)^n sum_j d_j,
    H(1)=2^n B[p](0)=2^n p(1)>=0.                                 (2)

Here B_m(0)=1 follows immediately from the defining recurrence, and
p(1)=2^n d_n>=0. The first identity follows by Cayley expansion: only
the degree-n input term remains at z=-1.

The alternating signs at -1,v_1,...,v_{n-1}, together with (2), give
one root in each of the first n-1 open intervals and one root in
(v_{n-1},1] (in the open interval if p(1)>0, at 1 if p(1)=0). There
are n distinct roots and degree at most n, so these are exactly all
the roots and all are simple. The inverse Cayley map sends (-1,1)
to (-infinity,0), and z=1 to x=0. This proves the theorem.

For n=1, the same argument uses only the two endpoint values. For n=0
the assertion reduces to a positive constant. The zero input is separate.

## The primary cone is contained in K_n

The original generators are t^(n-k)(t+1)^k. Write

    t = ((t-1)+(t+1))/2.

Expanding t^(n-k) with nonnegative binomial coefficients expresses each
generator as a nonnegative combination of the generators of K_n. Moreover
any nonzero original-cone input has p(1)=sum_k c_k 2^k>0, so all transformed
roots are strictly negative.

## The secondary derangement cone reduces to the same result

By its definition on monomials and linearity,

    D^B[p(t)] = B[p(t-1)].

For p(t)=sum_k c_k t^(n-k)(t+1)^k,

    p(t-1)=sum_k c_k(t-1)^(n-k)t^k.

The same identity t=((t-1)+(t+1))/2 gives p(t-1) in K_n. Thus D^B[p]
has n distinct nonpositive roots for every nonzero nonnegative coefficient
vector. Its constant term is p(0)=c_n, so all roots are strictly negative
if c_n>0, and exactly one root is zero if c_n=0.

This establishes the entire secondary cone statement independently of
the already-published result found in the literature search.
