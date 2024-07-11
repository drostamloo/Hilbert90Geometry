-- -*- coding: utf-8 -*-

newPackage(
		"Hilbert90Geometry",
		Version => "0.1",
		Date => "July 11, 2024",
		Headline => "Hilbert90Geometry, a package for computing geometries arising from the cyclic version of Hilbert's Theorem 90",
		Authors => {
		{Name => "Miles Kretschmer", Email => "mjkretschmer@uchicago.edu"}
		{Name => "Daniel Rostamloo", Email => "rostam@uw.edu", Homepage => "drostamloo.github.io"}}
		AuxiliaryFiles => false,
		DebuggingMode => true,
		PackageExports => {"RationalPoints2", "PushForward"}
		)

export {
	extAS
	}

-* Code section *-

extAS = method()
extAS(Ring) := (k) -> (
	p := char(ring);
	P := k[a,b,c];
	L := GF(p,p,Variable => x);
	R := ambient L;
	T := ambient R;
	I := module ideal R;
	S' := P[x];
	f' := map(S', T);
	I' := tensor(f', I);
	S := S'/I';

	f := map(S, P);
	(M, g, pf) = pushFwd(f)
)

(M,g,pf) = pushFwd(f)
pf(x+1)
pf((a + b*x + c*x^2)*x^2)
gal = matrix(k, {{1, 1, 1},{0, 1, -1},{0, 0, 1}})
gal * pf(a + b*x + c*x^2)
r = matrix(P, {{a,2c,2b},{b,a+c,b+2c},{c,b,a+c}})

-* Documentation section *-
beginDocumentation()

doc ///
Key
	Hilbert90Geometry
Headline
Description
	Text
	Tree
	Example
	CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
	Item
Description
	Text
	Example
	CannedExample
	Code
	Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///

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


load "RationalPoints2.m2"
load "PushForward.m2"

