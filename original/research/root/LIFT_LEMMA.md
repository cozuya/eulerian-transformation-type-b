# An additional proof of the vertical interlacing statement (L)

This lemma is not needed for the complete operator proof. It independently
settles the packet's vertical assertion for the main map:

\[
b(n-1,k)\prec b(n,k)\qquad(0\le k\le n-1).
\]

All roots in this statement are simple and negative. We prove the assertion
by induction over the rank. The case k=0 is the usual sign argument for the
defining type B recurrence. The rank-one assertion starts from the constant
b(0,0)=1 and b(1,0)=1+x.

Assume the assertions through rank n are known. For 1<=k<=n put

\[
g=b(n,k-1),\quad h=b(n-1,k-1),\quad f=b(n,k)=g+h.
\]

The induction hypothesis gives strict interlacing h≺g. At a root of h,
f=g, so the usual alternating-sign argument gives h≺f, with f having n
simple roots. They are negative because f has positive coefficients.

Write the roots of f as r_1,...,r_n. Strict interlacing and the degree
difference give the partial fraction expansion

\[
\frac{h(x)}{f(x)}=\sum_{i=1}^n\frac{\lambda_i}{x-r_i},
\qquad\lambda_i=\frac{h(r_i)}{f'(r_i)}>0.
\]

Evaluating at x=1 shows

\[
\frac{\lambda_i}{1-r_i}\le\frac{h(1)}{f(1)}.
\]

We need only a coarse bound on the right side. Since B_m(1)=2^m m!,

\[
b(n,k)(1)=\int_0^\infty e^{-t}(2t)^{n-k}(2t+1)^k\,dt.
\]

Integration by parts gives

\[
f(1)=\mathbf1_{n=k}+2(n-k)b(n-1,k)(1)+2k h(1),
\]

where the middle term is omitted when n=k. Hence f(1)>2k h(1), so

\[
k\lambda_i<\frac{1-r_i}{2}<1-r_i.
\]

The recurrence from the packet can be derived directly by expanding the
binomial definition:

\[
b(n+1,k)=(1+(2n+1)x)f+2x(1-x)f'-2kx h.
\]

At x=r_i it becomes

\[
b(n+1,k)(r_i)
=2r_i f'(r_i)\bigl((1-r_i)-k\lambda_i\bigr).
\]

The factor in parentheses is positive and r_i<0. Thus this value has the
opposite sign to f'(r_i). The positive leading coefficient and positive
constant term of b(n+1,k) supply the two end signs, yielding n+1 distinct
negative roots strictly interlacing f. This completes the induction.

No extra computation was run for this derivation. The rerun of the supplied
exact probe through n=18 separately corroborates this relation on that range.
