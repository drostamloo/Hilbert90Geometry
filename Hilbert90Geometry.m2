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
		PackageExports => {"RationalPoints2", "PushForward", "Cremona", "MultiprojectiveVarieties"}
		)

export {
	"extMod", -- produces either a degree n Kummer or Artin-Schreier extension over the smallest finite field of characteristic p with a primitive n-th root of unity as a module over the ground field via the pushFwd method
	"galExtMod", -- produces the matrix associated to the generator of a cyclic Galois group by reducing to either the Artin-Schreier or Kummer case
	"galExtModAS", -- the Artin-Schreier case of galExtMod
	"galExtModKummer", -- the Kummer case of galExtMod
	"multExtMod", -- produces the matrix over the ground field associated to multiplication by an element of the field extension with a choice of coefficients
	"hilbertCoordinates", -- produces matrices representing the coordinates of the mapping given by interpreting Hilbert's Theorem 90 geometrically, and its inverse
	"inverseTest" -- compute the rational map and its inverse and check if their compositions are equal to the identity on a dense open set
	}

-* Code section *-

extMod = method()
extMod(ZZ, ZZ) := (p, n) -> (
	t := symbol t;
	a := symbol a;
	x := symbol x;

	k := (ZZ/p)[t];
	k' := if p != n then extField(t^n-1, Variable => t) else ZZ/p;
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
	
	use L;
	z := traceSearch(n,f, x); -- element of nonzero trace 
	
	(L, K, f, M, g, pf, z)
)

traceSearch = method() -- check all powers of x, one must have nonzero trace
traceSearch(ZZ, RingMap, RingElement) := (n, f, x) -> (
	for i from 0 to n - 1 do (if trace(pushFwd(f, matrix{{x^i}})) != 0 then break x^i)
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
	n := numgens source coefs;
	fieldGens := matrix{apply(n, i -> (L_0)^i)};
	alpha := fieldGens * transpose(coefs); -- 1x1 matrix containing element of field extension coordinatized by coefs 

	pushFwd(f, alpha) -- pushing forward here yields an nxn matrix representing multiplication by the element
)

hilbertCoordinates = method()
hilbertCoordinates(ZZ, ZZ) := (p, n) -> (
	(L, K, f, M, g, pf, z) := extMod(p, n);
	gal := galExtMod(K, M);
	coefs := matrix{apply(n, i -> f(K_i))};
	mult := multExtMod(L, K, f, coefs);
	N := det mult;
	Tcoefs := transpose coefs;
	
	factors := multExtMod(L, K, f, coefs); -- initialize factors in product
	for i in 2..n do (
		factors *= multExtMod(L, K, f, transpose (gal^i * Tcoefs));
	);
	hilb := transpose(factors * transpose matrix{ join( {1}, for i in 2..n list 0)}) | matrix {{N}}; -- apply matrix to 1, take transpose, adjoin norm
	
	hTerms := new MutableList from (for i from 0 to n - 1 list gal^i); -- initialize a mutable list of terms in the sum for h operator
	for i from 0 to n - 1 do (
		for j from 0 to i-1 do (
			hTerms#i = multExtMod(L,K,f, transpose(gal^j * Tcoefs))*(hTerms#i); --left multiply by galois translates of generic element
		);
	);
	h := sum(new List from hTerms);
	inv := transpose(h * pf(z)); -- apply h to z, then take transpose

	(hilb, inv)
)


inverseTest = method()
inverseTest(ZZ, ZZ) := (p, n) -> (
	(hilb, inv) := hilbertCoordinates(p, n);
	R := ring hilb;
	y := symbol y;
	variables := join(for i in 0..(n-1) list R_i, {y});
	k := coefficientRing(R);
	S := k[variables];
	f := map(S, R);
	N := ideal(f(hilb_(0,n)) - y^n);
	S' := S/N;
	residue := map(S',S);

	phi := rationalMap(R, S', hilb);
	
	invHomogenized := homogenize(f(inv), y);
	invResidues := residue(invHomogenized);
	psi := rationalMap(S', R, invResidues);
	
	id1 := rationalMap(R,R);
	id2 := rationalMap(S',S');
		
	(phi, psi, phi*psi, psi*phi, phi*psi == id1, psi*phi == id2)
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
-- loadPackage "Cremona"
-- loadPackage "MultiprojectiveVarieties"
