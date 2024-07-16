-- -*- coding: utf-8 -*-

newPackage(
		"Hilbert90Geometry",
		Version => "0.1",
		Date => "July 11, 2024",
		Headline => "Hilbert90Geometry, a Macaulay2 package for computing geometries arising from the cyclic version of Hilbert's Theorem 90",
		Authors => {
		{Name => "Miles Kretschmer", Email => "mjkretschmer@uchicago.edu"},
		{Name => "Daniel Rostamloo", Email => "rostam@uw.edu", Homepage => "drostamloo.github.io"}},
		AuxiliaryFiles => false,
		DebuggingMode => true,
		PackageExports => {"RationalPoints2", "PushForward", "RationalMaps", "MultiprojectiveVarieties"}
		)

export {
	"extMod", -- produces either a degree n Kummer or Artin-Schreier extension over the smallest finite field of characteristic p with a primitive n-th root of unity as a module over the ground field via the pushFwd method
	"galExtMod", -- produces the matrix associated to the generator of a cyclic Galois group by reducing to either the Artin-Schreier or Kummer case
	"galExtModAS", -- the Artin-Schreier case of galExtMod
	"galExtModKummer", -- the Kummer case of galExtMod
	"multExtMod", -- produces the matrix over the ground field associated to multiplication by an element of the field extension with a choice of coefficients
	"hilbertCoordinates", -- produces a matrix representing the coordinates of the mapping given by interpreting Hilbert's Theorem 90 geometrically
	"isBirationalEmbedding" -- returns a pair of truth values indicating whether the rational map given by hilbertCoordinates is in fact birational or a closed embedding, respectively
	}

-* Code section *-

extMod = method()
extMod(ZZ, ZZ) := (p, n) -> (
	t := symbol t;
	a := symbol a;
	x := symbol x;

	k := (ZZ/p)[t];
	k' := extField(t^n-1, Variable=>t);
	K := k'[a_0 .. a_(n-1)];
	l := ambient GF(p,n,Variable => x);
	S := ambient l;
	I := module ideal l;
	S' := K[x];
	f' := map(S', S);
	I' := ideal tensor(f', I);
	L := S'/I';

	f := map(L, K);
	(M, g, pf) := pushFwd(f);
	(L, K, f, M, g, pf)
)

galExtMod = method()
galExtMod(Ring, Module) := (K, M) -> (
	p := char K;
	n := rank M;
	if p == n then galExtModAS(K, M) else galExtModKummer(K, M)
)

galExtModAS = method()
galExtModAS(Ring, Module) := (K, M) -> (
	n := rank M;
	map(K^n, n, (i,j) -> binomial(j,i))
)

galExtModKummer = method()
galExtModKummer(Ring, Module) := (K, M) -> (
	k' := baseRing K;
	t := k'_0;
	inc := map(K, k');
	n := rank M;
	zetas := for i in 0..(n-1) list inc(t^i);
	diagonalMatrix(K, zetas)
)

multExtMod = method()
multExtMod(Ring, Ring, RingMap, Matrix) := (L, K, f, coefs) -> (
	n := numgens K;
	fieldGens := matrix{apply(n, i -> (L_0)^i)};
	alpha := fieldGens * transpose(coefs); pushFwd(f, alpha)
)

hilbertCoordinates = method()
hilbertCoordinates(ZZ, ZZ) := (p, n) -> (
		(L, K, f, M, g, pf) := extMod(p, n);
		gal := galExtMod(K, M);
		coefs := matrix{for i in 0..(n-1) list f(K_i)};
		mult := multExtMod(L, K, f, coefs);
		N := det mult;
		Tcoefs := transpose coefs;
		factors := multExtMod(L, K, f, coefs);
		for i in 2..n do factors *= multExtMod(L, K, f, transpose (gal^i * Tcoefs));
		matrix {{N}} | transpose(factors * transpose matrix{ join( {1}, for i in 2..n list 0 ) })
)

isBirationalEmbedding = method()
isBirationalEmbedding(ZZ, ZZ) := (p, n) -> (
	hilb := hilbertCoordinates(p, n);
	R := ring hilb;
	y := symbol y;
	variables := join( for i in 0..(n-1) list R_i, {y} );
	S := ZZ/p[variables];
	f := map(S, R);
	N := ideal(f(hilb_(0,0)) - y^n);
	S' := S/N;
	X := Proj R;
	Y := Proj S';
	phi := rationalMapping(Y,X,hilb);

	(isBirationalMap phi, isEmbedding phi)
)

-* Documentation section *-
beginDocumentation()

-- doc ///
-- Key
-- 	Hilbert90Geometry
-- Headline
-- 	"Hilbert90Geometry, a Macaulay2 package for computing geometries arising from the cyclic version of Hilbert's Theorem 90"
-- Description
-- 	Text
-- 	Tree
-- 	Example
-- 	CannedExample
-- Acknowledgement
-- Contributors
-- References
-- Caveat
-- SeeAlso
-- Subnodes
-- ///
-- 
-- doc ///
-- Key
-- 	Test
-- Headline
-- 	"Test"
-- Usage
-- Inputs
-- Outputs
-- Consequences
-- 	Item
-- Description
-- 	Text
-- 	Example
-- 	CannedExample
-- 	Code
-- 	Pre
-- ExampleFiles
-- Contributors
-- References
-- Caveat
-- SeeAlso
-- ///

-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

-* Development section *-
restart
debug needsPackage "Hilbert90Geometry"
check "Hilbert90Geometry"

uninstallPackage "Hilbert90Geometry"
restart
installPackage "Hilbert90Geometry"
viewHelp "Hilbert90Geometry"

loadPackage "Hilbert90Geometry"
-- loadPackage "RationalPoints2"
-- loadPackage "PushForward"
-- loadPackage "RationalMaps"
-- loadPackage "MultiprojectiveVarieties"

p = 3; n = 5;

(L, K, f, M, g, pf) = extMod(p,n)
hilb = hilbertCoordinates(p,n)
R = ring hilb
variables = join( for i in 0..(n-1) list R_i, {y} )
S = ZZ/3[variables]
f = map(S, R)
N = ideal(f(hilb_(0,0)) - y^n)
S = S/N

X = Proj R
Y = Proj S 
phi = rationalMapping(Y,X,hilb)
I = radical baseLocusOfMap phi

src = Proj R/(radical baseLocusOfMap(phi))
S' = singularLocus I
dim S'


isBirationalMap phi
isEmbedding phi
isBirationalOntoImage phi
rationalPoints(I, Projective => true)
