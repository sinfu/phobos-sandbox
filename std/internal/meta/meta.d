// Written in the D programming language.

/**
Auxiliary and algorithm templates for template metaprogramming on compile-time
entities.  Compile-time entities include types, compile-time values, symbols,
and sequences of those entities.

All members in this module are defined in the implicit $(D meta) namespace
and cannot be used without the $(D meta) qualifier:
----------
import std.meta;

// Error! reverse is not defined. Use meta.reverse instead.
alias reverse!(double, "x", double, "y") Rev;

// Okay, qualified with meta.
alias meta.reverse!(double, "x", double, "y") Rev;
----------

Macros:
  WIKI = Phobos/StdMeta
 TITLE = std.meta

Source:      $(PHOBOSSRC std/_meta.d) (which is just a shell around
             $(PHOBOSSRC std/internal/_meta/_meta.d))
Copyright:   Copyright Shin Fujishiro 2010.
License:     $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0)
Authors:     Shin Fujishiro
 */
module std.internal.meta.meta;

//             Copyright Shin Fujishiro 2010.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)


// Introduce the symbols visible to user for unaryT etc.
import std.meta;


//----------------------------------------------------------------------------//
// Fundamental Templates
//----------------------------------------------------------------------------//


/**
Makes an alias of $(D E).

Params:
 E = A compile-time entity: type, compile-time value, or any symbol.

Example:
 Literal values can't be aliased directly.  Use $(D meta.Id) as follows:
----------
template Front(seq...)
{
    alias meta.Id!(seq[0]) Front;
}
alias Front!(10, 20, 30) front;
static assert(front == 10);
----------
 */
template Id(E)
{
    alias E Id;
}

/// ditto
template Id(alias E)
{
    alias E Id;
}


unittest
{
    int sym;

    alias Id!100 n;
    alias Id!int T;
    alias Id!sym s;
    static assert(n == 100);
    static assert(is(T == int));
    static assert(__traits(isSame, s, sym));

    // Test for run-time equivalence with "alias sym s;"
    assert(&s == &sym);
}

unittest    // doc example
{
    struct Scope
    {
        template Front(seq...)
        {
            alias meta.Id!(seq[0]) Front;
        }
    }
    alias Scope.Front Front;

    alias Front!(10, 20, 30) front;
    static assert(front == 10);
}



/**
Makes a sequence of compile-time entities.  The sequence is just an alias of
the template variadic arguments: $(D seq).

Examples:
----------
alias meta.Seq!(int, double, string) Types;

static assert(is(Types[0] == int));
static assert(is(Types[1] == double));
static assert(is(Types[2] == string));
----------

 The sequence may contain compile-time expressions.  The following example
 makes a sequence of constant integers $(D numbers) and embeds it into an
 array literal.
----------
alias meta.Seq!(10, 20, 30) numbers;
int[] arr = [ 0, numbers, 100 ];
assert(arr == [ 0, 10, 20, 30, 100 ]);
----------
 */
template Seq(seq...)
{
    alias seq Seq;
}


unittest
{
    alias meta.Seq!(int, double, string) Types;

    static assert(is(Types[0] == int));
    static assert(is(Types[1] == double));
    static assert(is(Types[2] == string));
}

unittest
{
    alias meta.Seq!(10, 20, 30) numbers;
    int[] arr = [ 0, numbers, 100 ];
    assert(arr == [ 0, 10, 20, 30, 100 ]);
}



/**
Synonym of $(D meta.Seq).

This template is specially made available in the global namespace.  That is,
$(D TypeSeq) can be used without the $(D meta) prefix.

Params:
 Types = Zero or more types making up the sequence.

Returns:
 Sequence of the given types.

Examples:
 Comparing type sequences with the $(D is) expression.
----------
alias TypeSeq!(int, double, string) A;
static assert( is(A == TypeSeq!(int, double, string)));
static assert(!is(A == TypeSeq!(string, int, double)));
static assert(!is(A == TypeSeq!()));
----------

 Declaring a sequence of variables.  Note that it's different from a so-called
 tuple and can't be nested.
----------
TypeSeq!(int, double, TypeSeq!(bool, string)) vars;
vars[0] = 10;
vars[1] = 5.0;
vars[2] = false;
vars[3] = "Abcdef";
----------
 */
template TypeSeq(Types...)
{
    alias Types TypeSeq;
}


unittest
{
    alias TypeSeq!(int, double, string) A;
    static assert( is(A == TypeSeq!(int, double, string)));
    static assert(!is(A == TypeSeq!(string, int, double)));
    static assert(!is(A == TypeSeq!()));
}

unittest
{
    TypeSeq!(int, double, TypeSeq!(bool, string)) vars;
    vars[0] = 10;
    vars[1] = 5.0;
    vars[2] = false;
    vars[3] = "Abcdef";
}



/**
$(D meta.pack) makes an atomic entity from a sequence, which is useful for
passing multiple sequences to a template.

Params:
 seq = Zero or more compile-time entities to _pack.

Example:
 The following code passes three separate sequences to $(D meta.transverse)
 using $(D meta.pack):
----------
// Query the 0-th element of each sequence.
alias meta.transverse!(0, meta.pack!(int, 32),
                          meta.pack!(double, 5.0),
                          meta.pack!(string, "hello.")) first;
static assert(is(first[0] == int));
static assert(is(first[1] == double));
static assert(is(first[2] == string));
----------
 */
template pack(seq...)
{
    /**
     * Returns the packed sequence: $(D seq).
     */
    alias seq expand;


    /**
     * Returns the number of entities: $(D seq.length).
     */
    enum size_t length = seq.length;


    /**
     * Extracts the $(D i)-th element of the packed sequence.
     */
    template at(size_t i) if (i < length)
    {
        alias Id!(seq[i]) at;
    }


    /* undocumented (used by meta.tag) */
    struct Tag;
}


unittest
{
    alias pack!() empty;
    static assert(empty.length == 0);

    int sym;
    alias pack!(20, int, sym) mixed;
    static assert(mixed.length == 3);
    static assert(mixed.expand[0] == 20);
    static assert(is(mixed.expand[1] == int));
    static assert(__traits(isSame, mixed.expand[2], sym));

    alias pack!( pack!(1,2), pack!(int,bool), pack!void ) nested;
    static assert(nested.length == 3);
}

unittest    // doc example
{
    alias meta.transverse!(0, meta.pack!(int, 32),
                              meta.pack!(double, 5.0),
                              meta.pack!(string, "hello.")) first;
    static assert(is(first[0] == int));
    static assert(is(first[1] == double));
    static assert(is(first[2] == string));
}



/* undocumented for now */
template tag(seq...)
{
    enum tag = (pack!seq.Tag*).mangleof;
}


unittest
{
    alias meta.Seq!(int, "value") AA;
    alias meta.Seq!(double, "number", 5.0) BB;

    static assert(meta.tag!AA == meta.tag!AA);
    static assert(meta.tag!AA != meta.tag!BB);
    static assert(meta.tag!BB == meta.tag!BB);
}



/**
Determines if $(D A) and $(D B) are the same entities.

$(D A) and $(D B) are compared in terms of their mangled names.  So, a
literal value $(D 10) and a CTFE capable property function returning $(D 10)
are considered different; literals are values and properties are symbols.
----------
struct S
{
    static @property int property() { return 10; }
}
static assert( meta.isSame!(10, 10));
static assert(!meta.isSame!(S.property, 10));
static assert( meta.isSame!(S.property, S.property));
----------

Returns:
 $(D true) if and only if $(D A) and $(D B) are the same entity.

Example:
 Comparing various entities.
----------
// Compare types.
struct MyType {}
static assert( meta.isSame!(int, int));
static assert(!meta.isSame!(MyType, double));

// Compare values.  Type is significant.
enum str = "abc";
static assert( meta.isSame!(str, "abc"));
static assert(!meta.isSame!(10, 10u));      // int and uint

// Compare symbols.
void fun() {}
static assert( meta.isSame!(fun, fun));
static assert(!meta.isSame!(fun, std));     // function and package
----------
 */
template isSame(A, B)
{
    enum isSame = is(A == B);
}

/// ditto
template isSame(A, alias B) if (!isType!B)
{
    enum isSame = false;
}

/// ditto
template isSame(alias A, B) if (!isType!A)
{
    enum isSame = false;
}

/// ditto
template isSame(alias A, alias B) if (!isType!A && !isType!B)
{
    enum isSame = is(pack!A.Tag == pack!B.Tag); // type <=> mangleof
}


unittest    // type vs type
{
    enum   E { a }
    struct S {}

    static assert(isSame!(int, int));
    static assert(isSame!(E, E));
    static assert(isSame!(S, S));

    static assert(!isSame!(const  int, int));
    static assert(!isSame!(shared int, int));

    static assert(!isSame!(int, E));
    static assert(!isSame!(E, S));
    static assert(!isSame!(S, int));
}

unittest    // value vs value
{
    struct S {}

    static assert(isSame!(100, 100));
    static assert(isSame!('A', 'A'));
    static assert(isSame!(S(), S()));
    static assert(isSame!("abc", "abc"));

    static assert(!isSame!(100, 'A'));
    static assert(!isSame!("abc", S()));
    static assert(!isSame!(100, 100u));
}

unittest    // symbol vs symbol
{
    void fun() {}
    void pun() {}

    static assert( isSame!(fun, fun));
    static assert( isSame!(pun, pun));
    static assert(!isSame!(fun, pun));

    static assert(isSame!(isSame, isSame));
    static assert(isSame!(   std,    std));

    static assert(!isSame!(fun, isSame));
    static assert(!isSame!(pun,    std));
}

unittest    // mismatch
{
    static assert(!isSame!(   int, isSame));
    static assert(!isSame!(isSame,    int));
    static assert(!isSame!(    40,    int));
    static assert(!isSame!(   int,     40));
    static assert(!isSame!(isSame,     40));
    static assert(!isSame!(    40, isSame));
}

unittest    // doc example (property)
{
    struct S
    {
        static @property int property() { return 10; }
    }
    static assert( meta.isSame!(10, 10));
    static assert(!meta.isSame!(S.property, 10));
    static assert( meta.isSame!(S.property, S.property));
}

unittest    // doc example
{
    struct MyType {}
    static assert( meta.isSame!(int, int));
    static assert(!meta.isSame!(MyType, double));

    enum str = "abc";
    static assert( meta.isSame!(str, "abc"));
    static assert(!meta.isSame!(10, 10u));

    void fun() {}
    static assert( meta.isSame!(fun, fun));
    static assert(!meta.isSame!(fun, std));
}



/**
These overloads serve partial application of $(D meta.isSame).

Example:
----------
// Bind double as the first argument.
alias meta.isSame!double isDouble;

static assert( isDouble!double);    // meta.isSame!(double, double)
static assert(!isDouble!int   );    // meta.isSame!(double, int)
----------
 */
template isSame(A)
{
    alias _isSameAs!A.isSame isSame;
}

/// ditto
template isSame(alias A)
{
    alias _isSameAs!A.isSame isSame;
}


private
{
    // The eponymous templates spec doesn't allow overloads, so we
    // do it manually.

    template _isSameAs(A)
    {
        template isSame(      B) { alias .isSame!(A, B) isSame; }
        template isSame(alias B) { alias .isSame!(A, B) isSame; }
    }
    template _isSameAs(alias A)
    {
        template isSame(      B) { alias .isSame!(A, B) isSame; }
        template isSame(alias B) { alias .isSame!(A, B) isSame; }
    }
}


unittest
{
    alias isSame!int Tx;
    static assert( Tx!int);
    static assert(!Tx!200);
    static assert(!Tx!std);

    alias isSame!200 Vx;
    static assert(!Vx!int);
    static assert( Vx!200);
    static assert(!Vx!std);

    alias isSame!std Sx;
    static assert(!Sx!int);
    static assert(!Sx!200);
    static assert( Sx!std);
}

unittest    // doc example
{
    alias meta.isSame!double isDouble;

    static assert( isDouble!double);
    static assert(!isDouble!int   );
}



/**
Returns $(D true) if and only if $(D E) is a type.

Example:
----------
alias meta.Seq!(int, "x",
                double, "y",
                string, "z") Mixed;

alias meta.filter!(meta.isType, Mixed) Types;
static assert(is(Types == TypeSeq!(int, double, string)));
----------
 */
template isType(E)
{
    enum isType = true;
}

/// ditto
template isType(alias E)
{
    enum isType = is(E);
}


unittest
{
    // Basic & qualified types.
    static assert(isType!(int));
    static assert(isType!(const int));
    static assert(isType!(shared int));
    static assert(isType!(immutable int));

    // User-defined types.
    enum   Enum   { a }
    struct Struct {}
    class  Class  {}
    static assert(isType!Enum);
    static assert(isType!Struct);
    static assert(isType!Class);
}

unittest    // doc example
{
    alias meta.Seq!(int, "x",
                    double, "y",
                    string, "z") Mixed;

    alias meta.filter!(meta.isType, Mixed) Types;
    static assert(is(Types == TypeSeq!(int, double, string)));
}



/**
Returns $(D true) if and only if $(D E) has a compile-time value.  Literals,
constants and CTFE-able property functions would pass the test.

Example:
----------
template increment(alias value) if (meta.isValue!value)
{
    enum increment = value + 1;
}
enum a = increment!10;
enum b = increment!increment;   // Error: negates the constraint
----------
 */
template isValue(E)
{
    enum isValue = false;
}

/// ditto
template isValue(alias E)
{
    static if (is(typeof(E) T) && !is(T == void))
    {
        // NOTE: Some errors are gagged only inside static-if.
        static if (__traits(compiles, Id!([ E ])))
            enum isValue = true;
        else
            enum isValue = false;
    }
    else
    {
        enum isValue = false;
    }
}


unittest
{
    static struct S
    {
        int member;

      @property:
        static int fun() { return 10; }
               int gun() { return 10; }
        static int hun();
    }

    // Literal values
    static assert(isValue!100);
    static assert(isValue!"abc");
    static assert(isValue!([ 1,2,3,4 ]));
    static assert(isValue!(S(32)));

    // Constants
    static immutable staticConst = "immutable";
    enum manifestConst = 123;
    static assert(isValue!staticConst);
    static assert(isValue!manifestConst);

    // CTFE
    static assert( isValue!(S.fun));
    static assert(!isValue!(S.gun));
    static assert(!isValue!(S.hun));

    // Non-values
    static assert(!isValue!int);
    static assert(!isValue!S);
    static assert(!isValue!isValue);

    int runtimeVar;
    static assert(!isValue!(runtimeVar));
}

unittest
{
    struct Scope
    {
        template increment(alias value) if (meta.isValue!value)
        {
            enum increment = value + 1;
        }
    }
    alias Scope.increment increment;
    static assert( __traits(compiles, increment!10));
    static assert(!__traits(compiles, increment!increment));
}



/**
Returns $(D true) if and only if $(D E) has a compile-time value implicitly
convertible to type $(D T).

Example:
----------
template increment(alias value) if (meta.isValue!(long, value))
{
    enum increment = value + 1;
}
enum a = increment!10;
enum b = increment!"me";    // Error: nonconvertible to long
----------
 */
template isValue(T, E)
{
    enum isValue = false;
}

/// ditto
template isValue(T, alias E)
{
    enum isValue = is(typeof(E) : T) && isValue!E;
}


unittest
{
    static immutable string immstr = "abc";
    string varstr;
    static assert( isValue!(string, ""));
    static assert( isValue!(string, immstr));
    static assert(!isValue!(string, varstr));
    static assert(!isValue!(string, 65536));
    static assert(!isValue!(string, string));
}

unittest
{
    struct Scope
    {
        template increment(alias value) if (meta.isValue!(long, value))
        {
            enum increment = value + 1;
        }
    }
    alias Scope.increment increment;
    static assert( __traits(compiles, increment!10));
    static assert(!__traits(compiles, increment!"me"));
}



/* undocumented for now */
template metaComp(entities...) if (entities.length == 2)
{
    enum metaComp = tag!(entities[0]) < tag!(entities[1]);
}


unittest
{
    static assert(metaComp!(10, 20));
    static assert(metaComp!(10, -5)); // Yes
    static assert(metaComp!(int, 5));

    alias sort!(metaComp,    int, "x", 10, double, "y", 20) s1;
    alias sort!(metaComp, double, "y", 20,    int, "x", 10) s2;
    static assert(tag!s1 == tag!(double, int, 10, 20, "x", "y"));
    static assert(tag!s2 == tag!(double, int, 10, 20, "x", "y"));
}



//----------------------------------------------------------------------------//
// Auxiliary Templates
//----------------------------------------------------------------------------//


// Installs a code evaluating expr and aliasing it with '_'.  The result
// can be an atomic entity or a sequence as expr returns.
private mixin template _installLambdaExpr(string expr)
{
    static if (__traits(compiles, _expectEmptySeq!(mixin("("~ expr ~")[0 .. 0]"))))
    {
        mixin("alias Seq!("~ expr ~") _;");     // sequence
    }
    else
    {
        mixin("alias  Id!("~ expr ~") _;");     // atomic entity
    }
}

private template _expectEmptySeq() {}



/**
Transforms a string representing a compile-time entity into a unary template
that returns the represented entity.

Params:
 expr = String representing a compile-time entity using a template parameter
        $(D a) or $(D A).

Returns:
 Unary template that evaluates $(D expr).

Examples:
----------
alias meta.unaryT!q{ const A } Constify;
static assert(is(Constify!int == const int));

alias meta.unaryT!q{ a.length } lengthof;
static assert(lengthof!([ 1,2,3,4,5 ]) == 5);
----------

 The generated template can return a sequence.
----------
import std.meta;
import std.typecons;

// Extracts the Types property of a Tuple instance.
alias meta.unaryT!q{ A.Types } expand;

alias expand!(Tuple!(int, double, string)) Types;
static assert(is(Types[0] == int));
static assert(is(Types[1] == double));
static assert(is(Types[2] == string));
----------

See_Also:
 $(D meta.lambda)
 */
template unaryT(string expr)
{
    alias unaryTGen!expr.unaryT unaryT;
}

template unaryT(alias templat)
{
    alias templat unaryT;
}


private template unaryTGen(string expr)
{
    // These elaborate frontends will give better error messages.
    template unaryT(alias a) { alias _unaryT!a._ unaryT; }
    template unaryT(      A) { alias _unaryT!A._ unaryT; }

    private template _unaryT(args...)
    {
        alias Id!(args[0]) a, A;
        mixin _installLambdaExpr!expr;      // installs '_'
    }
}


unittest
{
    alias unaryT!q{ a + 1 } increment;
    alias unaryT!q{ A* } Pointify;
    static assert(increment!10 == 11);
    static assert(is(Pointify!int == int*));
}

unittest    // Test for sequence return
{
    struct Tup(T...)
    {
        alias T Types;
    }
    alias unaryT!q{ A.Types } Expand;
    alias Expand!(Tup!(int, double, string)) IDS;
    static assert(is(IDS == Seq!(int, double, string)));

    // 1-sequence
    alias unaryT!q{ Seq!(a) } oneseq;
    static assert(oneseq!int.length == 1);

    // arrays are not sequences
    alias unaryT!q{ a[0 .. 2] } slice;
    static assert(slice!([1,2,3]) == [1,2]);
}

unittest    // doc examples
{
    alias meta.unaryT!q{ const A } Constify;
    static assert(is(Constify!int == const int));

    alias meta.unaryT!q{ a.length } lengthof;
    static assert(lengthof!([ 1,2,3,4,5 ]) == 5);
}



/**
Transforms a string representing a compile-time entity into a binary template
that returns the represented entity.

Params:
 expr = String representing a compile-time entity using two template
        parameters: $(D a, A) as the first one and $(D b, B) the second.

Returns:
 Binary template that evaluates $(D expr).

Example:
 This example uses the first parameter $(D a) as a value and the second one
 $(D B) as a type, and returns a value.
----------
alias meta.binaryT!q{ a + B.sizeof } accumSize;

enum n1 = accumSize!( 0,    int);
enum n2 = accumSize!(n1, double);
enum n3 = accumSize!(n2,  short);
static assert(n3 == 4 + 8 + 2);
----------

See_Also:
 $(D meta.lambda)
 */
template binaryT(string expr)
{
    alias binaryTGen!expr.binaryT binaryT;
}

template binaryT(alias templat)
{
    alias templat binaryT;
}


private template binaryTGen(string expr)
{
    template binaryT(AB...) if (AB.length == 2)
    {
        alias _binaryT!AB._ binaryT;
    }

    private template _binaryT(args...)
    {
        alias Id!(args[0]) a, A;
        alias Id!(args[1]) b, B;
        mixin _installLambdaExpr!expr;      // installs '_'
    }
}


unittest
{
    alias binaryT!q{ B[A] } Assoc;
    alias binaryT!q{ A[b] } ArrayA;
    alias binaryT!q{ B[a] } ArrayB;
    alias binaryT!q{ a / b } div;
    static assert(is(Assoc!(string, int) == int[string]));
    static assert(is(ArrayA!(int, 10) == int[10]));
    static assert(is(ArrayB!(10, int) == int[10]));
    static assert(div!(28, -7) == -4);
}

unittest    // Test for sequence return
{
    alias binaryT!q{ Seq!(a, b, 3) } ab3;
    static assert([ ab3!(10, 20) ] == [ 10, 20, 3 ]);
}

unittest    // doc example
{
    alias meta.binaryT!q{ a + B.sizeof } accumSize;
    enum n1 = accumSize!( 0,    int);
    enum n2 = accumSize!(n1, double);
    enum n3 = accumSize!(n2,  short);
    static assert(n3 == 4 + 8 + 2);
}

unittest    // bug 4431
{
    alias binaryT!q{ B[A] } Assoc;
    struct S {}
    static assert(is(Assoc!(int, S) == S[int]));
    static assert(is(Assoc!(S, int) == int[S]));
    static assert(is(Assoc!(S, S) == S[S]));
}



// Generic mixins for variadicT and lambda.  These templates install
// one-letter symbols aliasing template arguments or captures.
private
{
    mixin template _parameters(size_t n, size_t i = 0)
    {
        static if (i < n && i < 8)
        {
            mixin("alias Id!(args[i]) "~ "abcdefgh"[i] ~","
                                       ~ "ABCDEFGH"[i] ~";");
            mixin _parameters!(n, i + 1);
        }
    }

    mixin template _captures(size_t n, size_t i = 0)
    {
        static if (i < n && i < 8)
        {
            mixin("alias Id!(captures[i]) "~ "pqrstuvw"[i] ~","
                                           ~ "PQRSTUVW"[i] ~";");
            mixin _captures!(n, i + 1);
        }
    }
}


/**
Transforms a string representing an expression into a variadic template.
The expression can read variadic arguments via $(D args).

The expression can also use named parameters as $(D meta.unaryT), but
the number of implicitly-named parameters is limited up to eight:
$(D a, b, c, d, e, f, g) and $(D h) (plus capitalized ones) depending
on the number of arguments.

Params:
 fun = Expression string or template declaration.  The string may use
       named parameters $(D a) to $(D h), $(D A) to $(D H) and $(D args).

Returns:
 Variadic template that evaluates $(D fun).

Example:
----------
alias meta.variadicT!q{ meta.Seq!(args[1 .. $], A) } rotate1;

static assert([ rotate1!(1, 2, 3, 4) ] == [ 2, 3, 4, 1 ]);
----------

See_Also:
 $(D meta.lambda)
 */
template variadicT(string expr)
{
    alias variadicTGen!expr.variadicT variadicT;
}

template variadicT(alias templat)
{
    alias templat variadicT;
}


private template variadicTGen(string expr)
{
    template variadicT(args...) { alias _variadicT!args._ variadicT; }

    private template _variadicT(args...)
    {
        // @@@BUG4886@@@ workaround '+'
        mixin _parameters!(+args.length);
        mixin _installLambdaExpr!expr;      // installs '_'
    }
}


unittest
{
    alias variadicT!q{ a + b*c } addMul;
    static assert(addMul!(2,  3,  5) == 2 +  3* 5);
    static assert(addMul!(7, 11, 13) == 7 + 11*13);

    alias variadicT!q{ [ g, e, c, a, b, d, f, h ] } shuffle;
    static assert(shuffle!(1,2,3,4,5,6,7,8) == [ 7,5,3,1,2,4,6,8 ]);

    // Using uppercase parameters
    alias variadicT!q{ const(B)[A] } MakeConstAA;
    static assert(is(MakeConstAA!(int, double) == const(double)[int]));
    static assert(is(MakeConstAA!(int, string) == const(string)[int]));

    alias variadicT!q{ pack!(G, E, C, A, B, D, F, H) } Shuffle;
    static assert(tag!(Shuffle!(int, double, string, bool,
                                dchar, void*, short, byte))
                  == tag!(pack!(short, dchar, string, int,
                                double, bool, void*, byte)));

    // Mixing multicase parameters
    alias variadicT!q{ A[b][c] } Make2D;
    static assert(is(Make2D!(   int, 10, 20) ==    int[10][20]));
    static assert(is(Make2D!(double, 30, 10) == double[30][10]));

    // args
    alias variadicT!q{ +args.length } lengthof;
    static assert(lengthof!(1,2,3,4,5,6,7,8,9) == 9);
}

unittest    // Test for sequence return
{
    alias variadicT!q{ args[0 .. $/2] } halve;
    static assert([ halve!(1,2,3,4) ] == [ 1,2 ]);
}

unittest    // doc example
{
    alias meta.variadicT!q{ meta.Seq!(args[1 .. $], A) } rotate1;

    static assert([ rotate1!(1, 2, 3, 4) ] == [ 2, 3, 4, 1 ]);
}



/**
Transforms a string representing a template body into a variadic template.

$(D meta.lambda) is much like $(D meta.variadicT) as it's variadic and
parameters can be accessed via $(D args) and $(D a)-$(D h).  In addition,
$(D meta.lambda) also supports recursions and local entity _captures.

Params:
     decl = String representing a valid template body.  The body must
            declare a symbol $(D __) that represents the result of the
            template.  The result can be overloaded if it's a function
            or a template.

            The body may use named parameters $(D a) to $(D h), $(D A) to
            $(D H) and $(D args).  Also, named _captures $(D p) to $(D w),
            $(D P) to $(D W) and $(D captures) are available.

            The body may use a symbol $(D lambda) that refers to the
            generated template itself.

 captures = Local compile-time entities (types, values, templates etc.) to
            make available in the generated template.

Returns:
 Variadic template whose body is $(D decl) and evaluates to $(D __) declared
 in the body.

Recursion:

 The generated template itself is accessible from the string using an
 identifier $(D lambda), and you can define recursive templates:
----------
// Remove pointer 'stars' from every type in a sequence.  The generated
// template is passed to meta.map as a transoformer template.
alias meta.map!(meta.lambda!(
                   q{
                        static if (is(A T == T*))
                        {
                            alias lambda!T _;   // recursion
                        }
                        else
                        {
                            alias        A _;
                        }
                    }),
                int*, void**, short, double***) NoPointers;
static assert(is(NoPointers[0] == int));
static assert(is(NoPointers[1] == void));
static assert(is(NoPointers[2] == short));
static assert(is(NoPointers[3] == double));
----------

Captures:

 The template generated by $(D meta.lambda) can use local entities
 explicitly passed via the $(D captures) parameter.  Like template
 parameters, captured entities get named $(D p)-$(D w) and $(D P)-$(D W).
----------
struct Example(T, UU...)
{
    // Check if UU contains a type that implicitly convertible to T,
    // and issues an error if so.
    static if (meta.any!(meta.lambda!(
                            q{
                                 enum _ = is(A : P);
                             },
                             T),    // T is captured as 'P'
                         UU))
    {
        static assert(0, "At least one type in "~ UU.stringof ~" is "
                        ~"implicitly convertible to "~ T.stringof);
    }
}
Example!(int, string, double) Okay;
Example!(int, string,   bool) Error;    // Convertible: bool -> int
----------
 */
template lambda(string decl, captures...)
{
    alias lambdaGen!(decl, captures).lambda lambda;
}

private template lambdaGen(string decl, captures...)
{
    template lambda(args...) { alias _lambda!args._ lambda; }

 private:

    template _lambda(args...)
    {
        // @@@BUG4886@@@ workaround '+'
        mixin _parameters!(    +args.length);
        mixin _captures  !(+captures.length);
        mixin _body;
    }

    // Because decl uses named parameter symbols (which may or may not be
    // available depending on the number of arguments), it has to be mixed
    // in via this template to defer compiler's checks.
    mixin template _body()
    {
        mixin(decl);
    }
}


unittest
{
    alias lambda!(
           q{
                // alias
                alias A[] _;
            })
            DynArray;
    static assert(is(DynArray!int == int[]));

    alias lambda!(
           q{
                // private members and enum
                enum x = a*a + b*b;
                enum y = a*b;
                enum _ = [ x, y ];
            })
            hypot2Area;
    static assert(hypot2Area!(3, 4) == [ 25, 12 ]);

    alias lambda!(
           q{
                // overloads
                template _(    T) { alias A[T] _; }
                template _(int n) { alias A[n] _; }
            })
            Arrayizer;
    alias Arrayizer!int IntArrayizer;
    static assert(is(IntArrayizer!string == int[string]));
    static assert(is(IntArrayizer!1024 == int[1024]));
}

unittest    // Test for captures
{
    alias lambda!(
           q{
                // lowercase captures
                enum _ = [ p,q,r,s,t,u,v,w ] == [ 1,2,3,4,5,6,7,8 ];
            },
            1,2,3,4,5,6,7,8) testLowerCapts;
    static assert(testLowerCapts!());

    alias lambda!(
           q{
                // uppercase captures
                enum _ = is(P ==  byte) && is(Q ==  short) &&
                         is(R ==   int) && is(S ==   long) &&
                         is(T == ubyte) && is(U == ushort) &&
                         is(V ==  uint) && is(W ==  ulong);
            },
            byte, short, int, long,
            ubyte, ushort, uint, ulong) testUpperCapts;
    static assert(testUpperCapts!());

    alias lambda!(
           q{
                // variadic captures
                enum _ = [ captures ] == [ 1,2,3,4,5,6,7,8,9 ];
            },
            1,2,3,4,5,6,7,8,9) testVariadicCapts;
    static assert(testVariadicCapts!());
}

unittest    // Test for recursion
{
    alias lambda!(
           q{
                static if (a <= 0)
                    enum _ = 0;
                else
                    enum _ = a + lambda!(a - 1);
            }) sum;
    static assert(sum!9 == 45);
    static assert(sum!0 ==  0);
}

unittest    // doc example (captures)
{
    struct Example(T, UU...)
    {
        static if (meta.any!(meta.lambda!(
                                q{
                                     enum _ = is(A : P);
                                 },
                                 T),
                             UU))
        {
            static assert(0, "At least one type in "~ UU.stringof ~" is "
                            ~"implicitly convertible to "~ T.stringof);
        }
    }
    static assert( __traits(compiles, Example!(int, string, double) ));
    static assert(!__traits(compiles, Example!(int, string,   bool) ));
}

unittest    // doc example (recursion)
{
    alias meta.map!(meta.lambda!(
                       q{
                            static if (is(A T : T*))
                            {
                                alias lambda!T _;
                            }
                            else
                            {
                                alias        A _;
                            }
                        }),
                    int*, void**, short, double***) NoPointers;
    static assert(is(NoPointers[0] == int));
    static assert(is(NoPointers[1] == void));
    static assert(is(NoPointers[2] == short));
    static assert(is(NoPointers[3] == double));
}



/**
Binds $(D args) to the leftmost parameters of a template $(D templat).

Params:
 templat = Template or string that can be tranformed to a variadic template
           using $(D meta.variadicT).
    args = Zero or more template instantiation arguments to bind.

Returns:
 Template that instantiates $(D templat) with the bound arguments and
 additional ones as $(D templat!(args, ...)).

Example:
----------
template compareSize(T, U)
{
    enum compareSize = T.sizeof < U.sizeof;
}

// Get the types satisfying "int.sizeof < U.sizeof".
alias meta.filter!(meta.bind!(compareSize, int),
                   byte, double, short, int, long) Result;
static assert(is(Result == TypeSeq!(double, long) ));
----------
 */
template bind(alias templat, args...)
{
    template bind(rest...)
    {
        alias apply!(variadicT!templat, args, rest) bind;
    }
}


unittest
{
    alias bind!(q{ A[B] }) Assoc;
    alias bind!(q{ A[B] }, short) ShortAssoc;
    alias bind!(q{ A[B] }, int, double) IntDouble;
    static assert(is(Assoc!(uint, void*) == uint[void*]));
    static assert(is(ShortAssoc!string == short[string]));
    static assert(is(IntDouble!() == int[double]));
}

unittest    // doc example
{
    struct Scope
    {
        template compareSize(T, U)
        {
            enum compareSize = T.sizeof < U.sizeof;
        }
    }
    alias Scope.compareSize compareSize;

    alias meta.filter!(meta.bind!(compareSize, int),
                       byte, double, short, int, long) Result;
    static assert(is(Result == TypeSeq!(double, long) ));
}



/**
Same as $(D meta.bind) except that $(D meta.rbind) binds arguments to
rightmost parameters.

Params:
 templat = Template or string that can be tranformed to a variadic template
           using $(D meta.variadicT).
    args = Zero or more template instantiation arguments to bind.

Returns:
 Template that instantiates $(D templat) with the bound arguments and
 additional ones as $(D templat!(..., args)).

Example:
----------
template compareSize(T, U)
{
    enum compareSize = T.sizeof < U.sizeof;
}

// Get the types satisfying "T.sizeof < int.sizeof"
alias meta.filter!(meta.rbind!(compareSize, int),
                   byte, double, short, int, long) Result;
static assert(is(Result == TypeSeq!(byte, short) ));
----------
 */
template rbind(alias templat, args...)
{
    template rbind(rest...)
    {
        alias apply!(variadicT!templat, rest, args) rbind;
    }
}


unittest
{
    alias rbind!(q{ A[B] }) Assoc;
    alias rbind!(q{ A[B] }, short) AssocShort;
    alias rbind!(q{ A[B] }, int, double) IntDouble;
    static assert(is(Assoc!(uint, void*) == uint[void*]));
    static assert(is(AssocShort!string == string[short]));
    static assert(is(IntDouble!() == int[double]));
}

unittest    // doc example
{
    struct Scope
    {
        template compareSize(T, U)
        {
            enum compareSize = T.sizeof < U.sizeof;
        }
    }
    alias Scope.compareSize compareSize;

    alias meta.filter!(meta.rbind!(compareSize, int),
                       byte, double, short, int, long) Result;
    static assert(is(Result == TypeSeq!(byte, short) ));
}



/**
Binds $(D args) to all the parameters of $(D templat).  Generated template
will instantiate $(D templat) with just the bound arguments.

Params:
 templat = Template or string to instantiate.
    args = Complete arguments for $(D templat).

Returns:
 Variadic template that constantly returns $(D templat!args) regardless of
 its arguments.

Example:
----------
alias meta.delay!(meta.Id, int) Int;
static assert(is(Int!() == int));
static assert(is(Int!(void) == int));
static assert(is(Int!(1,2,3) == int));
----------

 Using a delayed template for a fallback case of $(D meta.guard):
----------
struct Error;

alias meta.guard!(q{ A[] }, meta.delay!(meta.Id, Error)) Array;
static assert(is(Array!int == int[]));
static assert(is(Array!100 == Error));
----------
 */
template delay(alias templat, args...)
{
    template delay(_...)
    {
        alias templat!args delay;
    }
}

template delay(string templat, args...)
{
    alias delay!(variadicT!templat, args) delay;
}


unittest
{
    alias delay!(Seq) empty;
    static assert(empty!().length == 0);
    static assert(empty!(int).length == 0);
    static assert(empty!(int, double).length == 0);

    alias delay!(q{ a + b }, 10, 20) sum30;
    static assert(sum30!() == 30);
    static assert(sum30!(40) == 30);
}

unittest    // doc example (1)
{
    alias meta.delay!(meta.Id, int) Int;
    static assert(is(Int!() == int));
    static assert(is(Int!(void) == int));
    static assert(is(Int!(1,2,3) == int));
}

unittest    // doc example (2)
{
    struct Error;

    alias meta.guard!(q{ A[] }, meta.delay!(meta.Id, Error)) Array;
    static assert(is(Array!int == int[]));
    static assert(is(Array!100 == Error));
}



/**
Generates a template that constantly evaluates to $(D E).

Params:
 E = Compile-time entity to hold.

Returns:
 Variadic template that ignores its arguments and just returns $(D E).

Example:
----------
alias meta.constant!int Int;
static assert(is(Int!() == int));
static assert(is(Int!(double, string) == int));
----------
 */
template constant(E)
{
    template constant(_...) { alias E constant; }
}

/// ditto
template constant(alias E)
{
    template constant(_...) { alias E constant; }
}

/// ditto
template constant()
{
    template constant(_...) { alias Seq!() constant; }
}


unittest
{
    alias constant!string String;
    static assert(is(String!() == string));
    static assert(is(String!(1,2,3) == string));
    static assert(is(String!(double, bool) == string));

    alias constant!512 number;
    static assert(number!() == 512);
    static assert(number!(1,2,3) == 512);
    static assert(number!(double, bool) == 512);

    alias constant!() empty;
    static assert(empty!().length == 0);
    static assert(empty!(1,2,3).length == 0);
    static assert(empty!(double, bool).length == 0);
}

unittest    // doc example
{
    alias meta.constant!int Int;
    static assert(is(Int!() == int));
    static assert(is(Int!(double, string) == int));
}



/**
Creates a predicate template that inverts the result of the given one.

Params:
 pred = Predicate template or expression string to invert.  The result
        must be a compile-time value that is implicitly convertible to
        $(D bool) in conditional expressions.

Returns:
 Template that evaluates $(D pred) and returns an inverted result.

Example:
 Passing an inverted predicate to the $(D meta.countIf).
----------
template isStruct(T)
{
    enum isStruct = is(T == struct) || is(T == union);
}

struct S {}
union  U {}
class  C {}

// Count non-struct types in the sequence.
enum n = meta.countIf!(meta.not!isStruct,
                       int, double, S, U, C);
static assert(n == 3);
----------
 */
template not(alias pred)
{
    template not(args...)
    {
        enum not = !pred!args;
    }
}

/// ditto
template not(string pred)
{
    alias not!(variadicT!pred) not;
}


unittest
{
    alias not!(isSame!int) notInt;
    static assert( notInt!double);
    static assert( notInt!"none");
    static assert(!notInt!int   );

    // double invert
    alias not!notInt isInt;
    static assert(!isInt!double);
    static assert(!isInt!"none");
    static assert( isInt!int   );
}

unittest
{
    alias not!"a == 5" notFive;
    static assert( notFive!4);
    static assert( notFive!6);
    static assert(!notFive!5);

    alias not!notFive isFive;
    static assert(!isFive!4);
    static assert(!isFive!6);
    static assert( isFive!5);
}

unittest    // doc example
{
    struct Scope
    {
        template isStruct(T)
        {
            enum isStruct = is(T == struct) || is(T == union);
        }
    }
    alias Scope.isStruct isStruct;

    struct S {}
    union  U {}
    class  C {}

    enum n = meta.countIf!(meta.not!isStruct,
                           int, double, S, U, C);
    static assert(n == 3);
}



/**
Composes predicate templates with the logical $(D &&) operator.

The predicates will be evaluated in the same order as passed to this
template.  The evaluations are lazy; if one of the predicates is not
satisfied, $(D meta.and) immediately returns $(D false) without evaluating
remaining predicates.

Params:
 preds = Zero or more predicate templates to compose.  This argument can be
         empty; in that case, the resulting template constantly evaluates to
         $(D true).

Returns:
 Composition predicate template that tests if its arguments satisfy all the
 predicates $(D preds).

Example:
----------
alias meta.and!(meta.isType, q{ is(A : long) }, q{ A.min < 0 }) isSignedInt;
static assert( isSignedInt!short);
static assert( isSignedInt!int);
static assert(!isSignedInt!uint);
static assert(!isSignedInt!string);     // stops at the second predicate
static assert(!isSignedInt!"wrong");    // stops at the first predicate
----------
 */
template and(preds...)
{
    alias reduce!(.and, preds) and;
}

template and(alias pred1 = constant!true,
             alias pred2 = constant!true)
{
    template and(args...)
    {
        static if (apply!(pred1, args) && apply!(pred2, args))
            enum and = true;
        else
            enum and = false;
    }
}


unittest
{
    struct Scope
    {
        template isConst(T) { enum isConst = is(T == const); }
    }
    alias Scope.isConst isConst;

    // Compose nothing
    alias and!() yes;
    static assert(yes!());
    static assert(yes!(1, 2, 3));

    // No actual composition
    alias and!isConst isConst2;
    static assert( isConst2!(const int));
    static assert(!isConst2!(      int));

    alias and!q{ a < 0 } isNeg;
    static assert( isNeg!(-1));
    static assert(!isNeg!( 0));

    // Compose template and string
    alias and!(isConst, q{ A.sizeof < 4 }) isTinyConst;
    static assert( isTinyConst!(const short));
    static assert(!isTinyConst!(      short));
    static assert(!isTinyConst!(const   int));
    static assert(!isTinyConst!(        int));
}

unittest    // doc example
{
    alias meta.and!(meta.isType, q{ is(A : long) }, q{ A.min < 0 }) isSignedInt;
    static assert( isSignedInt!short);
    static assert( isSignedInt!int);
    static assert(!isSignedInt!uint);
    static assert(!isSignedInt!string);
    static assert(!isSignedInt!"wrong");
}



/**
Composes predicate templates with the logical $(D ||) operator.

The predicates will be evaluated in the same order as passed to this
template.  The evaluations are lazy; if one of the predicates is
satisfied, $(D meta.or) immediately returns $(D true) without evaluating
remaining predicates.

Params:
 preds = Zero or more predicate templates to compose.  This argument can be
         empty; in that case, the resulting template constantly evaluates to
         $(D false).

Returns:
 Composition predicate template that tests if its arguments satisfy at least
 one of the predicates $(D preds).

Example:
----------
// Note that bool doesn't have the .min property.
alias meta.filter!(meta.or!(q{ A.sizeof < 4 }, q{ A.min < 0 }),
                   bool, ushort, int, uint) R;
static assert(is(R == TypeSeq!(bool, ushort, int)));
----------
 */
template or(preds...)
{
    alias reduce!(.or, preds) or;
}

template or(alias pred1 = constant!false,
            alias pred2 = constant!false)
{
    template or(args...)
    {
        static if (apply!(pred1, args) || apply!(pred2, args))
            enum or = true;
        else
            enum or = false;
    }
}


unittest
{
    struct Scope
    {
        template isConst(T)
        {
            enum isConst = is(T == const);
        }
    }
    alias Scope.isConst isConst;

    // Compose nothing
    alias or!() no;
    static assert(!no!());

    // No actual composition
    alias or!isConst isConst2;
    static assert( isConst2!(const int));
    static assert(!isConst2!(      int));

    alias or!q{ a < 0 } isNeg;
    static assert( isNeg!(-1));
    static assert(!isNeg!( 0));

    // Compose template and string
    alias or!(isConst, q{ A.sizeof < 4 }) isTinyOrConst;
    static assert( isTinyOrConst!(const short));
    static assert( isTinyOrConst!(      short));
    static assert( isTinyOrConst!(const   int));
    static assert(!isTinyOrConst!(        int));
}

unittest    // doc example
{
    alias meta.filter!(meta.or!(q{ A.sizeof < 4 }, q{ A.min < 0 }),
                       bool, ushort, int, uint) R;
    static assert(is(R == TypeSeq!(bool, ushort, int)));
}



/**
$(D meta.compose!(t1, t2, ..., tn)) returns a variadic template that in
turn instantiates the passed in templates in a chaining way:
----------
template composition(args...)
{
    alias t1!(t2!( ... tn!(args) ... )) composition;
}
----------

Params:
 templates = One or more templates making up the chain.  Each template
             can be a template or a string; strings are transformed to
             varadic templates using $(D meta.variadicT).

Returns:
 New template that instantiates the chain of $(D templates).

Example:
----------
alias meta.compose!(q{ A[] },
                    q{ const A }) ConstArray;
static assert(is(ConstArray!int == const(int)[]));
----------
 */
template compose(templates...)
{
    alias reduce!(.compose, templates) compose;
}

template compose(alias template1 = Seq,
                 alias template2 = Seq)
{
    template compose(args...)
    {
        // NOTE: Templates might be strings.
        alias apply!(template1, apply!(template2, args)) compose;
    }
}


unittest
{
    struct Scope
    {
        template Const(T) { alias const(T) Const; }
        template Array(T) { alias T[] Array; }
    }
    alias Scope.Const Const;
    alias Scope.Array Array;

    // No actual composition
    alias compose!Const Const1;
    alias compose!q{ a * 7 } mul1;
    static assert(is(Const1!int == const int));
    static assert(mul1!11 == 77);

    // Two templates
    alias compose!(Array, Const) ArrayConst;
    static assert(is(ArrayConst!int == const(int)[]));

    alias compose!(Seq, q{ a / b }) SeqDiv;
    static assert(SeqDiv!(77, 11).length == 1);
    static assert(SeqDiv!(77, 11)[0] == 7);

    alias compose!(q{ [ args ] }, reverse) arrayRev;
//  static assert(arrayRev!(1,2,3) == [ 3,2,1 ]);   // @@@BUG3276@@@

    // More compositions
    alias compose!(q{ a * 11 }, q{ a + 7 }, q{ -a }) mul11add7neg;
    static assert(mul11add7neg!(-6) == (6 + 7) * 11);
}

unittest    // doc example
{
    alias meta.compose!(q{ A[] },
                        q{ const A }) ConstArray;
    static assert(is(ConstArray!int == const(int)[]));
}



/**
Generates a template that tries instantiating specified templates in turn
and returns the result of the first compilable template.

For example, $(D meta.guard!(t1, t2)) generates a template that behaves
as follows:
----------
template trial(args...)
{
    static if (__traits(compiles, t1!(args)))
    {
        alias t1!(args) trial;
    }
    else
    {
        alias t2!(args) trial;
    }
}
----------

Params:
 templates = Templates to try instantiation.  Each template can be a real
             template or a string that can be transformed to a template
             using $(D meta.variadicT).

Returns:
 Variadic template that instantiates the first compilable template among
 $(D templates).  The last template is not guarded; if all the templates
 failed, the generated template will fail due to the last one.

Example:
----------
alias meta.guard!(q{ A.min < 0 }, q{ false }) hasNegativeMin;
static assert( hasNegativeMin!int);
static assert(!hasNegativeMin!uint);
static assert(!hasNegativeMin!void);    // void.min is not defined!
----------
 */
template guard(templates...) if (templates.length > 0)
{
    alias reduce!(.guard, templates) guard;
}

template guard(alias template1, alias template2)
{
    template guard(args...)
    {
        static if (__traits(compiles, apply!(template1, args)))
        {
            alias apply!(template1, args) guard;
        }
        else
        {
            alias apply!(template2, args) guard;
        }
    }
}

template guard(alias templat)
{
    template guard(args...)
    {
        alias apply!(templat, args) guard;
    }
}


unittest
{
    struct Scope
    {
        template Const(T) { alias const(T) Const; }
    }
    alias Scope.Const Const;

    // No actual guard
    alias guard!Const JustConst;
    static assert(is(JustConst!int == const int));
    static assert(!__traits(compiles, JustConst!10));

    alias guard!q{ a + 1 } increment;
    static assert(increment!13 == 14);
    static assert(!__traits(compiles, increment!double));

    // Double trial
    alias guard!(Const, Id) MaybeConst;
    static assert(is(MaybeConst!int == const int));
    static assert(MaybeConst!"string" == "string");

    alias guard!(q{ +a }, q{ A.init }) valueof;
    static assert(valueof!1.0 == 1.0);
    static assert(valueof!int == 0);

    // Triple trial
    alias guard!(q{ [a] }, q{ [A.min]  }, q{ [A.init] }) makeArray;
    static assert(makeArray!1.0 == [ 1.0 ]);
    static assert(makeArray!int == [ int.min ]);
    static assert(makeArray!string == [ "" ]);
}

unittest     // doc example
{
    alias meta.guard!(q{ A.min < 0 }, q{ false }) hasNegativeMin;
    static assert( hasNegativeMin!int);
    static assert(!hasNegativeMin!double);
    static assert(!hasNegativeMin!void);
}



/**
Generates a template that conditionally instantiates either $(D then) or
$(D otherwise) depending on the result of $(D pred).

Params:
      pred = Predicate template.
      then = Template to instantiate when $(D pred) is satisfied.
 otherwise = Template to instantiate when $(D pred) is not satisfied.

Returns:
 Variadic template that instantiates $(D then) with its arguments if the
 arguments satisfy $(D pred), or instantiates $(D otherwise) with the same
 arguments if not.

Example:
----------
import std.meta, std.traits, std.typecons;

alias meta.conditional!(q{ is(A == class) }, Rebindable, Unqual) NoTopConst;

static assert(is( NoTopConst!(const Object) == Rebindable!(const Object) ));
static assert(is( NoTopConst!(const int[]) == const(int)[] ));
static assert(is( NoTopConst!(const int) == int ));
----------
 */
template conditional(alias pred, alias then, alias otherwise = meta.Id)
{
    alias _conditional!(variadicT!pred,
                        variadicT!then,
                        variadicT!otherwise).conditional conditional;
}

private template _conditional(alias pred, alias then, alias otherwise)
{
    template conditional(args...)
    {
        static if (pred!args)
        {
            alias then!args conditional;
        }
        else
        {
            alias otherwise!args conditional;
        }
    }
}


unittest
{
    alias conditional!(q{  true }, q{ const A }, q{ immutable A }) Const;
    alias conditional!(q{ false }, q{ const A }, q{ immutable A }) Imm;
    static assert(is(Const!double ==     const double));
    static assert(is(  Imm!double == immutable double));

    alias conditional!(isType, q{ A }, q{ typeof(a) }) LooseTypeof;
    static assert(is(LooseTypeof!int == int));
    static assert(is(LooseTypeof!"abc" == string));

    // Using default 'otherwise'
    alias conditional!(q{ is(A == immutable) }, q{ A[] }) ImmArray;
    static assert(is(ImmArray!int == int));
    static assert(is(ImmArray!string == string));
    static assert(is(ImmArray!(immutable int) == immutable(int)[]));
}

unittest    // doc example
{
    struct Unqual(T) {}
    struct Rebindable(T) {}

    alias meta.conditional!(q{ is(A == class) }, Rebindable, Unqual) NoHeadConst;

    static assert(is( NoHeadConst!(const Object) == Rebindable!(const Object) ));
    static assert(is( NoHeadConst!(const int[]) == Unqual!(const int[]) ));
    static assert(is( NoHeadConst!(const int) == Unqual!(const int) ));
}



/* undocumented (for internal use) */
template compiles(templates...)
{
    template compiles(args...)
    {
        enum compiles = __traits(compiles, map!(applier!args, templates));
    }
}



/**
Instantiates $(D templat) with the specified arguments.

Params:
 templat = Template to instantiate.  The argument can be a pure template or
           a string that can be transformed into a pure template using
           $(D meta.variadicT).
    args = The instantiation arguments to pass to $(D templat).

Returns:
 The result: $(D templat!args).

Example:
 Due to a syntactical limitation of the language, templates generated by
 higher-order templates (such as $(D meta.guard)) can't be instantiated
 directly.  Use $(D meta.apply) to instantiate such kind of temporary templates.
----------
template Example(Arg)
{
    static if (meta.apply!(meta.guard!(q{ A.min < 0 },
                                       q{     false }), Arg))
    {
        // ...
    }
}
----------
 */
template apply(alias templat, args...)
{
    alias templat!args apply;
}

/// ditto
template apply(string templat, args...)
{
    alias apply!(variadicT!templat, args) apply;
}



/* undocumented (for internal use) */
template applier(args...)
{
    template applier(alias templat)
    {
        alias apply!(templat, args) applier;
    }
}


unittest
{
    alias applier!() empty;
    static assert( tag!(empty!Seq ) == tag!( Seq!()) );
    static assert( tag!(empty!pack) == tag!(pack!()) );

    alias applier!(int, 100) int100;
    static assert( tag!(int100!pack) == tag!(pack!(int, 100)) );
    static assert( tag!(int100!q{ const A }) == tag!(const int) );
}



//----------------------------------------------------------------------------//
// Sequence Construction
//----------------------------------------------------------------------------//


/**
Expands a compile-time array into a sequence of the elements.

Params:
 arr = Compile-time expression of an array.  The array can be dynamic or
       static.  The length and elements must be known at compile-time.

Returns:
 Sequence of the elements of $(D arr).

Example:
 Using $(D meta.expand) to apply a meta algorithm $(D meta.map) on
 elements of a compile-time array.
----------
enum functions = [ "fun", "gun", "hun" ];

// Use meta.map to transform the function names into signatures with
// help of meta.expand.
alias meta.map!(meta.lambda!(
                   q{
                        // Make a signature of a variadic function of
                        // the given name 'a'.
                        enum _ = "auto "~ a ~"(Args...)(Args args)";
                    }),
                meta.expand!functions) signatures;

static assert(signatures[0] == "auto fun(Args...)(Args args)");
static assert(signatures[1] == "auto gun(Args...)(Args args)");
static assert(signatures[2] == "auto hun(Args...)(Args args)");
----------
 */
template expand(alias arr)
{
    static if (arr.length == 0)
    {
        alias Seq!() expand;
    }
    else static if (arr.length == 1)
    {
        alias Seq!(arr[0]) expand;
    }
    else
    {
        // Halving array reduces the recursion depth.
        alias Seq!(expand!(arr[ 0  .. $/2]),
                   expand!(arr[$/2 ..  $ ])) expand;
    }
}


unittest
{
    static assert( tag!(expand!([])) == tag!() );
    static assert( tag!(expand!([1])) == tag!(1) );
    static assert( tag!(expand!([1,2,3,4])) == tag!(1,2,3,4) );

    // type check
    static assert(is( typeof(expand!([1.0,2.0])[0]) == double ));
    static assert(is( typeof(expand!([1.0,2.0])[1]) == double ));
}

unittest    // doc example
{
    enum functions = [ "fun", "gun", "hun" ];

    alias meta.map!(meta.lambda!(
                       q{
                            enum _ = "auto "~ a ~"(Args...)(Args args)";
                        }),
                    meta.expand!functions) signatures;
    static assert(signatures[0] == "auto fun(Args...)(Args args)");
    static assert(signatures[1] == "auto gun(Args...)(Args args)");
    static assert(signatures[2] == "auto hun(Args...)(Args args)");
}



/**
Yields a sequence of numbers starting from $(D beg) to $(D end) with the
specified $(D step).

Params:
  beg = Compile-time numeral value ($(D 0) if not specified).  The generated
        sequence starts with $(D beg) if not empty.

  end = Compile-time numeral value.  The resulting sequence stops before
        $(D end) and never contain this value.

 step = Compile-time numeral value ($(D 1) if not specified).  The generated
        sequence increases or decreases by $(D step).  This value may not
        be zero or NaN.

Returns:
 Sequence of compile-time numbers starting from $(D beg) to $(D end),
 increasing/decreasing by $(D step).  The generated sequence is empty if
 $(D beg) is ahead of $(D end) in terms of the $(D step)'s direction.

Examples:
 Filling array elements using $(D meta.iota):
----------
static Base64Chars = cast(immutable char[64])
    [
        meta.iota!('A', 'Z'+1),
        meta.iota!('a', 'z'+1),
        meta.iota!('0', '9'+1), '+', '/'
    ];
static assert(Base64Chars[16] == 'Q');
static assert(Base64Chars[32] == 'g');
static assert(Base64Chars[62] == '+');
----------

 So-called static foreach:
----------
void shift(Args...)(ref Args args)
{
    foreach (i; meta.iota!(1, +args.length))
    {
        args[i - 1] = args[i];
    }
    args[$ - 1] = args[$ - 1].init;
}

double a;
int    b = 10;
ushort c = 20;

shift(a, b, c);
assert(a == 10);
assert(b == 20);
assert(c ==  0);
----------
 */
template iota(alias beg, alias end, alias step) if (step <> 0)
{
    static if ((end - beg) / step >= 0)
    {
        alias _iota!(beg, step).upto!end iota;
    }
    else
    {
        alias Seq!() iota;
    }
}

/// ditto
template iota(alias beg, alias end)
{
    alias iota!(beg, end, cast(typeof(beg)) 1) iota;
}

/// ditto
template iota(alias end)
{
    alias iota!(cast(typeof(end)) 0, end) iota;
}


unittest    // doc example (array filling)
{
    static Base64Chars = cast(immutable char[64])
        [
            meta.iota!('A', 'Z'+1),
            meta.iota!('a', 'z'+1),
            meta.iota!('0', '9'+1), '+', '/'
        ];
    static assert(Base64Chars[16] == 'Q');
    static assert(Base64Chars[32] == 'g');
    static assert(Base64Chars[62] == '+');
}

unittest    // doc example (static foreach)
{
    void shift(Args...)(ref Args args)
    {
        foreach (i; meta.iota!(1, +args.length))    // @@@BUG4886@@@
        {
            args[i - 1] = args[i];
        }
        args[$ - 1] = args[$ - 1].init;
    }

    double a;
    int    b = 10;
    ushort c = 20;

    shift(a, b, c);
    assert(a == 10);
    assert(b == 20);
    assert(c ==  0);
}



private // iota for integral numbers
{
    template _isIntegralIota(alias beg, alias step)
    {
        enum _isIntegralIota = is(typeof( beg) : long) &&
                               is(typeof(step) : long);
    }

    template _iota(alias beg, alias step) if (_isIntegralIota!(beg, step))
    {
        template upto(alias end)
        {
            alias recurrence!(count!end, increment, beg) upto;
        }

     private:

        alias typeof(true ? beg : step) T;

        template count(alias end)
        {
            static if (step > 0)
                enum count = cast(size_t) ((end - beg + step - 1) / step);
            else
                enum count = cast(size_t) ((end - beg + step + 1) / step);
        }

        template increment(alias cur) { enum T increment = cur + step; }
    }
}


unittest
{
    static assert([ iota!0 ] == []);
    static assert([ iota!1 ] == [ 0 ]);
    static assert([ iota!2 ] == [ 0,1 ]);
    static assert([ iota!3 ] == [ 0,1,2 ]);
    static assert([ iota!(-1) ] == []);
    static assert([ iota!(-2) ] == []);

    static assert([ iota!(-5,  5) ] == [ -5,-4,-3,-2,-1,0,1,2,3,4 ]);
    static assert([ iota!( 5, -5) ] == []);
    static assert([ iota!(-5, -5) ] == []);

    static assert([ iota!( 3,  20, +4) ] == [  3, 7, 11, 15, 19 ]);
    static assert([ iota!(-3, -20, -4) ] == [ -3,-7,-11,-15,-19 ]);
    static assert([ iota!(1, 5, +9) ] == [ 1 ]);
    static assert([ iota!(5, 1, -9) ] == [ 5 ]);
    static assert([ iota!(3, 5, -1) ] == []);
    static assert([ iota!(5, 3, +1) ] == []);
    static assert([ iota!(3, 3, -1) ] == []);
}



private // iota for floating-point numbers
{
    template _isFloatingIota(alias beg, alias step)
    {
        enum _isFloatingIota = !_isIntegralIota!(beg, step) &&
                               (is(typeof( beg) : real) ||
                                is(typeof(step) : real));
    }

    template _iota(alias beg, alias step) if (_isFloatingIota!(beg, step))
    {
        template upto(alias end)
        {
            alias map!(transform, _iota!(0, 1).upto!(count!end)) upto;
        }

     private:

        alias typeof(true ? beg : step) T;

        template count(alias end)
        {
            // Dumb 'ceil' function.
            static if ((step > 0 && transform!(basicCount!end) < end) ||
                       (step < 0 && transform!(basicCount!end) > end))
                enum count = basicCount!end + 1;
            else
                enum count = basicCount!end;
        }

        template basicCount(alias end)
        {
            enum basicCount = cast(size_t) ((end - beg) / step);
        }

        template transform(alias cur) { enum T transform = beg + cur*step; }
    }
}


unittest
{
    static assert([ iota!(0.0) ] == []);
    static assert([ iota!(0.5) ] == [ 0.0 ]);
    static assert([ iota!(1.0) ] == [ 0.0 ]);
    static assert([ iota!(3.5) ] == [ 0.0, 1.0, 2.0, 3.0 ]);
    static assert([ iota!(-0.1) ] == []);
    static assert([ iota!(-5.5) ] == []);

    static assert([ iota!(-1.5,  4) ] == [ -1.5, -0.5, 0.5, 1.5, 2.5, 3.5 ]);
    static assert([ iota!( 5.0,  3) ] == []);
    static assert([ iota!(-0.9, -1) ] == []);

    static assert([ iota!(1.0, 3.01, 1) ] == [ 1.0, 2.0, 3.0 ]);
    static assert([ iota!(1.0, 1.5, 10) ] == [ 1.0 ]);
    static assert([ iota!(2.0, 1.5, -10) ] == [ 2.0 ]);
    static assert([ iota!(2.0, 10, -1) ] == []);
}



/**
Generates a sequence by repeatedly applying $(D fun) on generated elements,
and takes the first $(D n) results:
----------
meta.recurrence!(n, fun, Seed) = (Seed, fun!Seed, fun!(fun!Seed), ...)
----------

Params:
    n = Number of recurrences.  Specify zero to get the empty sequence.
  fun = Recurrence template that computes the next state.  The state can be
        any sequence which can be passed to $(D fun) itself.
 Seed = Initial state.

Returns:
 Sequence composed of $(D Seed) followed by $(D fun!Seed), $(D fun!(fun!Seed)),
 ... etc., ending with the $(D n-1) repeated application of $(D fun).

Example:
----------
alias meta.recurrence!(4, q{ A* }, int) Pointers;
static assert(is(Pointers == TypeSeq!(int, int*, int**, int***)));
----------
 */
template recurrence(size_t n, alias fun, Seed...)
{
    static if (n < 2)
    {
        alias Seed[0 .. n * $] recurrence;
    }
    else
    {
        alias Seq!(Seed, recurrence!(n - 1, fun, apply!(fun, Seed))) recurrence;
    }
}


unittest
{
    static assert([ recurrence!(0, q{ a*5 }, 1) ] == [ ]);
    static assert([ recurrence!(1, q{ a*5 }, 1) ] == [ 1 ]);
    static assert([ recurrence!(2, q{ a*5 }, 1) ] == [ 1,5 ]);
    static assert([ recurrence!(5, q{ a*5 }, 1) ] == [ 1,5,25,125,625 ]);

    alias recurrence!(3, q{ Seq!(args, void) }, int) VI;
    static assert(is(VI == TypeSeq!(int, int, void, int, void, void)));
}

unittest    // doc example
{
    alias meta.recurrence!(4, q{ A* }, int) Pointers;
    static assert(is(Pointers == TypeSeq!(int, int*, int**, int***)));
}



/**
Creates a sequence in which $(D seq) repeats $(D n) times.

Params:
   n = The number of repetition.  May be zero.
 seq = Sequence to _repeat.

Returns:
 Sequence composed of $(D n) $(D seq)s.  The empty sequence is returned
 if $(D n) is zero or $(D seq) is empty.

Example:
----------
static immutable array =
    [
        meta.repeat!(3, 1,2,3),
        meta.repeat!(3, 4,5,6),
    ];
static assert(array == [ 1,2,3, 1,2,3, 1,2,3,
                         4,5,6, 4,5,6, 4,5,6 ]);
----------
 */
template repeat(size_t n, seq...)
{
    static if (n < 2 || seq.length == 0)
    {
        alias seq[0 .. n*$] repeat;
    }
    else
    {
        // Halving n reduces the recursion depth.
        alias Seq!(repeat!(   n    / 2, seq),
                   repeat!((n + 1) / 2, seq)) repeat;
    }
}


unittest
{
    // degeneracy
    static assert(is(repeat!(0) == Seq!()));
    static assert(is(repeat!(1) == Seq!()));
    static assert(is(repeat!(9) == Seq!()));
    static assert(is(repeat!(0, int        ) == Seq!()));
    static assert(is(repeat!(0, int, double) == Seq!()));

    // basic
    static assert(is(repeat!( 1, int, double) == Seq!(int, double)));
    static assert(is(repeat!( 2, int, double) == Seq!(int, double,
                                                      int, double)));
    static assert(is(repeat!( 3, int, double) == Seq!(int, double,
                                                      int, double,
                                                      int, double)));
    static assert(is(repeat!( 9, int) == Seq!(int, int, int, int,
                                              int, int, int, int, int)));
    static assert(is(repeat!(10, int) == Seq!(int, int, int, int, int,
                                              int, int, int, int, int)));

    // expressions
    static assert([0, repeat!(0, 8,7), 0] == [0,                  0]);
    static assert([0, repeat!(1, 8,7), 0] == [0, 8,7,             0]);
    static assert([0, repeat!(3, 8,7), 0] == [0, 8,7,8,7,8,7,     0]);
    static assert([0, repeat!(4, 8,7), 0] == [0, 8,7,8,7,8,7,8,7, 0]);
}

unittest
{
    static immutable array =
        [
            meta.repeat!(3, 1,2,3),
            meta.repeat!(3, 4,5,6),
        ];
    static assert(array == [ 1,2,3, 1,2,3, 1,2,3,
                             4,5,6, 4,5,6, 4,5,6 ]);
}



/* undocumented (for internal use) */
template replaceAt(size_t i, E, seq...)
{
    alias Seq!(seq[0 .. i], E, seq[i + 1 .. $]) replaceAt;
}

template replaceAt(size_t i, alias E, seq...)
{
    alias Seq!(seq[0 .. i], E, seq[i + 1 .. $]) replaceAt;
}


unittest
{
    static assert([ replaceAt!(0, 0, 1,2,3,4,5) ] == [ 0,2,3,4,5 ]);
    static assert([ replaceAt!(2, 0, 1,2,3,4,5) ] == [ 1,2,0,4,5 ]);
    static assert([ replaceAt!(4, 0, 1,2,3,4,5) ] == [ 1,2,3,4,0 ]);

    alias replaceAt!(0, int, 1,2,3,4,5) T0;
    alias replaceAt!(2, int, 1,2,3,4,5) T2;
    alias replaceAt!(4, int, 1,2,3,4,5) T4;
    static assert(tag!T0 == tag!(int,2,3,4,5));
    static assert(tag!T2 == tag!(1,2,int,4,5));
    static assert(tag!T4 == tag!(1,2,3,4,int));
}



/**
Swaps $(D i)-th and $(D j)-th elements of $(D seq).

Params:
   i = Valid index for $(D seq).
   j = ditto.
 seq = Target sequence.

Returns:
 $(D seq) in which $(D seq[i]) and $(D seq[j]) are replaced with each other.

Example:
----------
alias TypeSeq!(byte, short, int, long) Types;

// Swap short and int.
alias meta.swapAt!(1, 2, Types) Swapped;
static assert(is(Swapped == TypeSeq!(byte, int, short, long)));
----------
 */
template swapAt(size_t i, size_t j, seq...)
{
    alias replaceAt!(j, seq[i], replaceAt!(i, seq[j], seq)) swapAt;
}


unittest
{
    static assert([ swapAt!(1, 3, 0,1,2,3,4) ] == [ 0,3,2,1,4 ]);
    static assert([ swapAt!(0, 3, 0,1,2,3,4) ] == [ 3,1,2,0,4 ]);
    static assert([ swapAt!(4, 1, 0,1,2,3,4) ] == [ 0,4,2,3,1 ]);
    static assert([ swapAt!(4, 0, 0,1,2,3,4) ] == [ 4,1,2,3,0 ]);
    static assert([ swapAt!(1, 1, 0,1,2,3,4) ] == [ 0,1,2,3,4 ]);
}



/* undocumented (for internal use) */
template extractAt(size_t i, seq...)
{
    alias Id!(seq[i]) extractAt;
}


/**
Extracts elements at the specified positions out of $(D seq).

Params:
 indices = Compile-time array of _indices designating elements to _extract.
           Each index must be less than $(D seq.length) and implicitly
           convertible to $(D size_t).  Duplicate _indices are allowed.

     seq = Source sequence.

Returns:
 Sequence of elements extracted from $(D seq).  The order of the elements
 is the same as that of corresponding _indices in $(D indices).  The length
 of the result is the same as that of $(D indices), and the empty sequence
 is returned if $(D indices) is empty.

Example:
----------
alias TypeSeq!(double, "value", 5.0) seq;
alias meta.extract!([ 0, 2 ], seq) extracted;

static assert(extracted.length == 2);
static assert(is(extracted[0] == double));
static assert(   extracted[1] == 5.0    );
----------
 */
template extract(alias indices, seq...)
{
    alias map!(rbind!(extractAt, seq), expand!indices) extract;
}


unittest
{
    alias Seq!(0,10,20,30,40) src;

    static assert([ extract!([], src) ] == [ ]);
    static assert([ extract!([2], src) ] == [ 20 ]);
    static assert([ extract!([1,2,3], src) ] == [ 10,20,30 ]);
    static assert([ extract!([0,1,2,3,4], src) ] == [ 0,10,20,30,40 ]);
    static assert([ extract!([0,1,2,3,4], src) ] == [ 0,10,20,30,40 ]);

    static assert([ extract!([1,1,1], src) ] == [ 10,10,10 ]);
    static assert([ extract!([3,3,3,2,2,2], src) ] == [ 30,30,30,20,20,20 ]);
}



/* undocumented (used by stride) */
template frontof(seq...)
{
    alias Id!(seq[0]) frontof;
}



//----------------------------------------------------------------------------//
// Topological Transformation
//----------------------------------------------------------------------------//


/**
Reverses the sequence $(D seq).

Params:
 seq = Sequence to _reverse.

Returns:
 $(D seq) in the _reverse order.

Example:
----------
alias meta.reverse!(int, double, string) Rev;
static assert(is(Rev == TypeSeq!(string, double, int)));
----------
 */
template reverse(seq...)
{
    static if (seq.length < 2)
    {
        alias seq reverse;
    }
    else
    {
        // Halving seq reduces the recursion depth.
        alias Seq!(reverse!(seq[$/2 ..  $ ]),
                   reverse!(seq[ 0  .. $/2])) reverse;
    }
}


unittest
{
    static assert(is(reverse!() == Seq!()));

    // basic
    static assert(is(reverse!(int) == Seq!(int)));
    static assert(is(reverse!(int, double) == Seq!(double, int)));
    static assert(is(reverse!(int, double, string) ==
                         Seq!(string, double, int)));
    static assert(is(reverse!(int, double, string, bool) ==
                         Seq!(bool, string, double, int)));

    // expressions
    static assert([0, reverse!(),        0] == [0,          0]);
    static assert([0, reverse!(1),       0] == [0, 1,       0]);
    static assert([0, reverse!(1,2),     0] == [0, 2,1,     0]);
    static assert([0, reverse!(1,2,3),   0] == [0, 3,2,1,   0]);
    static assert([0, reverse!(1,2,3,4), 0] == [0, 4,3,2,1, 0]);
}



/**
Rotates $(D seq) by $(D n).  If $(D n) is positive and less than $(D seq),
the result is $(D (seq[n .. $], seq[0 .. n])).

Params:
   n = The amount of rotation.  The sign determines the direction:
       positive for left rotation and negative for right rotation.
       This argument can be zero or larger than $(D seq.length).
 seq = Sequence to _rotate.

Returns:
 Sequence $(D seq) rotated by $(D n).

Example:
----------
alias meta.rotate!(+1, int, double, string) rotL;
alias meta.rotate!(-1, int, double, string) rotR;

static assert(meta.tag!rotL == meta.tag!(double, string, int));
static assert(meta.tag!rotR == meta.tag!(string, int, double));
----------
 */
template rotate(sizediff_t n, seq...)
{
    static if (seq.length < 2)
    {
        alias seq rotate;
    }
    else
    {
        static if (n < 0)
        {
            alias rotate!(seq.length + n, seq) rotate;
        }
        else
        {
            alias Seq!(seq[n % $ .. $], seq[0 .. n % $]) rotate;
        }
    }
}


unittest
{
    alias rotate!(0) empty0;
    alias rotate!(0, int) single0;
    alias rotate!(0, int, double, string) triple0;
    static assert(is( empty0 == Seq!()));
    static assert(is(single0 == Seq!(int)));
    static assert(is(triple0 == Seq!(int, double, string)));

    alias rotate!(+2) empty2;
    alias rotate!(+2, int) single2;
    alias rotate!(+2, int, double, string) triple2;
    static assert(is( empty2 == Seq!()));
    static assert(is(single2 == Seq!(int)));
    static assert(is(triple2 == Seq!(string, int, double)));

    alias rotate!(-2) empty2rev;
    alias rotate!(-2, int) single2rev;
    alias rotate!(-2, int, double, string) triple2rev;
    static assert(is( empty2rev == Seq!()));
    static assert(is(single2rev == Seq!(int)));
    static assert(is(triple2rev == Seq!(double, string, int)));
}



/**
Gets the elements of sequence with _stride $(D n).

Params:
   n = Stride width.  $(D n) must not be zero.
 seq = Sequence to _stride.

Returns:
 Sequence of $(D 0,n,2n,...)-th elements of the given sequence:
 $(D (seq[0], seq[n], seq[2*n], ...)).  The empty sequence is returned if the
 given sequence $(D seq) is empty.

Example:
----------
alias meta.Seq!(int, "index", 10,
                double, "number", 5.0) seq;
alias meta.stride!(3, seq        ) Types;
alias meta.stride!(3, seq[1 .. $]) names;

static assert(meta.tag!Types == meta.tag!(int, double));
static assert(meta.tag!names == meta.tag!("index", "number"));
----------
 */
template stride(size_t n, seq...) if (n >= 1)
{
    alias segmentWith!(frontof, n, seq) stride;
}


unittest
{
    static assert(is(stride!(1) == Seq!()));
    static assert(is(stride!(2) == Seq!()));
    static assert(is(stride!(5) == Seq!()));

    alias stride!(1, int, double, string) asis;
    static assert(tag!asis == tag!(int, double, string));

    static assert([ stride!(2, 1,2,3,4,5) ] == [ 1,3,5 ]);
    static assert([ stride!(3, 1,2,3,4,5) ] == [ 1,4 ]);
    static assert([ stride!(5, 1,2,3,4,5) ] == [ 1 ]);
}

unittest
{
    alias meta.Seq!(int, "index", 10,
                    double, "number", 5.0) seq;
    alias meta.stride!(3, seq        ) Types;
    alias meta.stride!(3, seq[1 .. $]) names;

    static assert(meta.tag!Types == meta.tag!(int, double));
    static assert(meta.tag!names == meta.tag!("index", "number"));
}



/**
Splits sequence $(D seq) into segments of the same length $(D n).

Params:
   n = The size of each _segment.  $(D n) must not be zero.
 seq = Sequence to split.  The sequence can have arbitrary length.

Returns:
 Sequence of packed segments of length $(D n).  Each segment is packed using
 $(D meta.pack); use the $(D expand) property to yield the contents.

 The last _segment can be shorter than $(D n) if $(D seq.length) is not an
 exact multiple of $(D n).  The empty sequence is returned if $(D seq) is
 empty.

Example:
 $(D meta.segment) would be useful to scan simple patterns out of
 template parameters or other sequences.
----------
alias meta.Seq!(int, "index", 10,
                double, "number", 5.0) seq;

alias meta.segment!(3, seq) patterns;
static assert(meta.isSame!(patterns[0], meta.pack!(int, "index", 10)));
static assert(meta.isSame!(patterns[1], meta.pack!(double, "number", 5.0)));
----------
 */
template segment(size_t n, seq...) if (n >= 1)
{
    alias segmentWith!(pack, n, seq) segment;
}


unittest
{
    alias segment!(1) empty1;
    alias segment!(9) empty9;
    static assert(empty1.length == 0);
    static assert(empty9.length == 0);

    alias segment!(1, 1,2,3,4) seg1;
    alias segment!(2, 1,2,3,4) seg2;
    alias segment!(3, 1,2,3,4) seg3;
    static assert(tag!seg1 == tag!(pack!(1), pack!(2), pack!(3), pack!(4)));
    static assert(tag!seg2 == tag!(pack!(1,2), pack!(3,4)));
    static assert(tag!seg3 == tag!(pack!(1,2,3), pack!4));
}

unittest
{
    alias meta.Seq!(int, "index", 10,
                    double, "number", 5.0) seq;

    alias meta.segment!(3, seq) patterns;
    static assert(meta.isSame!(patterns[0], meta.pack!(int, "index", 10)));
    static assert(meta.isSame!(patterns[1], meta.pack!(double, "number", 5.0)));
}



/**
Generalization of $(D meta.segment) passing each segment to $(D fun) instead
of $(D meta.pack).

Params:
 fun = $(D n)-ary template that transforms each segment.
   n = The size of each _segment.  $(D n) must not be zero.
 seq = Sequence to process.

Returns:
 Sequence of the results of $(D fun) applied to each segment.

Example:
----------
alias meta.segmentWith!(q{ B[A] }, 2,
                        string, int, string, double) result;
static assert(is(result[0] ==    int[string]));
static assert(is(result[1] == double[string]));
----------
 */
template segmentWith(alias fun, size_t n, seq...) if (n == 1)
{
    alias map!(fun, seq) segmentWith;
}

/// ditto
template segmentWith(alias fun, size_t n, seq...) if (n > 1)
{
    static if (seq.length == 0)
    {
        alias Seq!() segmentWith;
    }
    else static if (seq.length <= n)
    {
        alias Seq!(apply!(fun, seq)) segmentWith;
    }
    else
    {
        // Halving seq reduces the recursion depth.
        alias Seq!(segmentWith!(fun, n, seq[0 .. _segmentMid!($, n)     ]),
                   segmentWith!(fun, n, seq[     _segmentMid!($, n) .. $]))
              segmentWith;
    }
}


// Computes the proper bisecting point.
private template _segmentMid(size_t n, size_t k)
{
    enum _segmentMid = ((n + k - 1) / k / 2) * k;
}


unittest
{
    alias segmentWith!(pack, 1) empty1;
    alias segmentWith!(pack, 5) empty5;
    static assert(empty1.length == 0);
    static assert(empty5.length == 0);

    alias segmentWith!(q{ a*2 }, 1,
                       1,2,3,4,5,6) doubled;
    static assert([ doubled ] == [ 2,4,6,8,10,12 ]);

/+  @@@BUG3276@@@
    alias segmentWith!(reverse, 2,
                       1,2,3,4,5,6,7,8,9) rev2;
    static assert([ rev2 ] == [ 2,1,4,3,6,5,8,7,9 ]);
+/
}

unittest
{
    alias meta.segmentWith!(q{ B[A] }, 2,
                            string, int, string, double) result;
    static assert(is(result[0] ==    int[string]));
    static assert(is(result[1] == double[string]));
}



/**
Given sequence of packed sequences, generates a sequence transversing
the $(D i)-th element of each of the sequences.

Params:
    i = Valid index for each packed sequence in $(D seqs).
 seqs = Sequence of packed sequences.  Each packed sequence must have a
        property $(D expand) that yields a sequence and its length must be
        greater than $(D i).

Returns:
 Sequence composed of the $(D i)-th element of each of the given sequences.

Example:
----------
alias meta.transverse!(1, meta.pack!(int, 255),
                          meta.pack!(double, 7.5),
                          meta.pack!(string, "yo")) second;
static assert(meta.tag!second == meta.tag!(255, 7.5, "yo"));
----------
 */
template transverse(size_t i, seqs...) if (isTransversable!(i, seqs))
{
    alias map!(unpackAt!i, seqs) transverse;
}

private
{
    template unpackAt(size_t i)
    {
        template unpackAt(alias pak) { alias pak.expand[i .. i+1] unpackAt; }
    }

    template isTransversable(size_t i, seqs...)
    {
        enum isTransversable = all!(compiles!(unpackAt!i), seqs);
    }
}


unittest
{
    alias transverse!0 empty0;
    alias transverse!9 empty9;
    static assert(empty0.length == 0);
    static assert(empty9.length == 0);

    alias transverse!(0, pack!(int, double, string)) single0;
    alias transverse!(2, pack!(int, double, string)) single2;
    static assert(is(single0 == Seq!int));
    static assert(is(single2 == Seq!string));

    alias transverse!(1, pack!(1,2), pack!(3,4,5), pack!(6,7)) jagged;
    static assert([ jagged ] == [ 2,4,7 ]);

    static assert(!__traits(compiles, transverse!(0, 1,2,3) ));
    static assert(!__traits(compiles, transverse!(0, pack!1, pack!()) ));
}

unittest
{
    alias meta.transverse!(1, meta.pack!(int, 255),
                              meta.pack!(double, 7.5),
                              meta.pack!(string, "yo")) second;
    static assert(meta.tag!second == meta.tag!(255, 7.5, "yo"));
}



/**
Generates a sequence iterating given sequences in lockstep.  The iteration
stops on encountering the end of the shortest sequence.

Params:
 seqs = Sequence of packed sequences.  Each packed sequence must have a
        property $(D expand) that yields a sequence.

Returns:
 Sequence of the transversals of $(D seqs), each of which is the result of
 $(D meta.transversal) packed in a $(D meta.pack).  The empty sequence is
 returned if $(D seqs) is empty or any of the sequences is empty.

Example:
----------
alias meta.zip!(meta.pack!(int, 255),
                meta.pack!(double, 7.5),
                meta.pack!(string, "yo")) zipped;
static assert(meta.isSame!(zipped[0], meta.pack!(int, double, string)));
static assert(meta.isSame!(zipped[1], meta.pack!(255, 7.5, "yo")));
----------
 */
template zip(seqs...) if (isZippable!seqs)
{
    alias zipWith!(pack, seqs) zip;
}

private
{
    template isZippable(seqs...)
    {
        static if (_minLength!seqs == 0)
            enum isZippable = true;
        else
            enum isZippable = isTransversable!(_minLength!seqs - 1, seqs);
    }

    template _minLength(seqs...)
    {
        static if (seqs.length == 0)
            enum _minLength = 0;
        else
            enum _minLength = _shortest!seqs.length;
    }

    template _shortest(seqs...) if (seqs.length > 0)
    {
        alias most!(q{ a.length < b.length }, seqs) _shortest;
    }
}


unittest
{
    alias zip!() empty;
    static assert(empty.length == 0);

    alias zip!(pack!(int, double, bool), pack!(4, 8, 1)) zip3;
    static assert(zip3.length == 3);
    static assert(isSame!(zip3[0], pack!(   int, 4)));
    static assert(isSame!(zip3[1], pack!(double, 8)));
    static assert(isSame!(zip3[2], pack!(  bool, 1)));

    alias zip!(pack!(int, double, string),
               pack!("i", "x"),
               pack!(5, 1.5, "moinmoin")) jagged;
    static assert(jagged.length == 2);
    static assert(isSame!(jagged[0], pack!(   int, "i",   5)));
    static assert(isSame!(jagged[1], pack!(double, "x", 1.5)));

    alias zip!(pack!int, pack!(), pack!(double, string)) degen;
    static assert(degen.length == 0);
}

unittest
{
    alias meta.zip!(meta.pack!(int, 255),
                    meta.pack!(double, 7.5),
                    meta.pack!(string, "yo")) zipped;
    static assert(meta.isSame!(zipped[0], meta.pack!(int, double, string)));
    static assert(meta.isSame!(zipped[1], meta.pack!(255, 7.5, "yo")));
}



/**
Generalization of $(D meta.zip) passing each transversal to $(D fun), instead
of packing with $(D meta.pack).

Params:
  fun = Template of arity $(D seqs.length) that transforms each transversal.
 seqs = Sequence of packed sequences.

Returns:
 Sequence of the results of $(D fun) applied to each transversal of $(D seqs).

Example:
----------
alias meta.pack!("int", "double", "string") types;
alias meta.pack!(  "i",      "x",      "s") names;
alias meta.zipWith!(q{ a~" "~b }, types, names) zipped;

static assert(zipped[0] == "int i");
static assert(zipped[1] == "double x");
static assert(zipped[2] == "string s");
----------
 */
template zipWith(alias fun, seqs...) if (isZippable!seqs)
{
    alias map!(_transverser!(variadicT!fun, seqs), iota!(_minLength!seqs)) zipWith;
}

private template _transverser(alias fun, seqs...)
{
    template _transverser(size_t i)
    {
        alias fun!(transverse!(i, seqs)) _transverser;
    }
}


unittest
{
    static struct MyPack(int n, T);

/+  @@@BUG3276@@@
    alias zipWith!(compose!(MyPack, reverse),
                   pack!(int, double, string),
                   pack!(  1,      2,      3)) revzip;
    static assert(is(revzip[0] == MyPack!(1,    int)));
    static assert(is(revzip[1] == MyPack!(2, double)));
    static assert(is(revzip[2] == MyPack!(3, string)));
+/

    alias zipWith!(q{ A[B] },
                   pack!(  int, double, string),
                   pack!(dchar, string,    int)) assoc;
    static assert(is(assoc[0] ==    int[ dchar]));
    static assert(is(assoc[1] == double[string]));
    static assert(is(assoc[2] == string[   int]));
}

unittest
{
    alias meta.pack!("int", "double", "string") types;
    alias meta.pack!(  "i",      "x",      "s") names;
    alias meta.zipWith!(q{ a~" "~b }, types, names) zipped;

    static assert(zipped[0] == "int i");
    static assert(zipped[1] == "double x");
    static assert(zipped[2] == "string s");
}



//----------------------------------------------------------------------------//
// Elements Transformation
//----------------------------------------------------------------------------//


/**
Transforms a sequence $(D seq) into $(D (fun!(seq[0]), fun!(seq[1]), ...)).

Params:
 fun = Unary template used to transform each element of $(D seq) into another
       compile-time entity.  The result can be a sequence.
 seq = Sequence of compile-time entities to transform.

Returns:
 Sequence of the results of $(D fun) applied to each element of $(D seq) in
 turn.

Examples:
 Map types into pointers.
----------
alias meta.map!(q{ A* }, int, double, void*) PP;
static assert(is(PP[0] ==    int*));
static assert(is(PP[1] == double*));
static assert(is(PP[2] ==  void**));
----------

 Doubling elements:
----------
static assert([ meta.map!(q{ meta.Seq!(a, a) }, 1,2,3) ] == [ 1,1, 2,2, 3,3 ]);
----------
 */
template map(alias fun, seq...)
{
    static if (seq.length == 1)
    {
        alias Seq!(fun!(seq[0])) map;
    }
    else
    {
        // Halving seq reduces the recursion depth.
        alias Seq!(map!(fun, seq[ 0  .. $/2]),
                   map!(fun, seq[$/2 ..  $ ])) map;
    }
}

/// ditto
template map(string fun, seq...)
{
    alias map!(unaryT!fun, seq) map;
}


template map(alias  fun) { alias Seq!() map; }
template map(string fun) { alias Seq!() map; }


unittest
{
    static assert(map!(Id).length == 0);
    static assert(map!(q{ a }).length == 0);

    alias map!(Id, int) single;
    static assert(is(single == Seq!int));

    alias map!(q{ const A }, int) const1;
    static assert(is(const1 == Seq!(const int)));

    alias map!(q{ 2*a }, 1,2,3,4,5) double5;
    static assert([ double5 ] == [ 2,4,6,8,10 ]);
}

unittest
{
    alias meta.map!(q{ A* }, int, double, void*) PP;
    static assert(is(PP[0] ==    int*));
    static assert(is(PP[1] == double*));
    static assert(is(PP[2] ==  void**));

    static assert([ meta.map!(q{ meta.Seq!(a, a) }, 1,2,3) ] == [ 1,1, 2,2, 3,3 ]);
}



/* Recursive map, used by uniqBy */
template mapRec(alias fun, seq...)
{
    alias _mapRec!(variadicT!fun).mapRec!seq mapRec;
}

private template _mapRec(alias fun)
{
    template mapRec(seq...)
    {
        alias fun!(seq[0], mapRec!(seq[1 .. $])) mapRec;
    }

    template mapRec()
    {
        alias Seq!() mapRec;
    }
}



/**
Creates a sequence only containing elements of $(D seq) satisfying $(D pred).

Params:
 pred = Unary predicate template that decides whether or not to include an
        element in the resulting sequence.
  seq = Sequence to _filter.

Returns:
 Sequence only containing elements of $(D seq) for each of which $(D pred)
 evaluates to $(D true).

Example:
----------
alias meta.filter!(q{ A.sizeof < 4 }, byte, short, int, long) SmallTypes;
static assert(is(SmallTypes == TypeSeq!(byte, short)));
----------
 */
template filter(alias pred, seq...)
{
    alias map!(conditional!(pred, Id, constant!()), seq) filter;
}


unittest
{
    alias filter!(isType) empty;
    static assert(empty.length == 0);

    alias filter!(isType, 1,2,3) none;
    alias filter!(isValue, 1,2,3) all;
    static assert([ none ] == []);
    static assert([ all ] == [ 1,2,3 ]);

    alias filter!(isType, int, "x", double, "y") someT;
    static assert(is(someT == Seq!(int, double)));

    alias filter!(q{ a < 0 }, 4, -3, 2, -1, 0) someV;
    static assert([ someV ] == [ -3, -1 ]);
}

unittest
{
    alias meta.filter!(q{ A.sizeof < 4 }, byte, short, int, long) SmallTypes;
    static assert(is(SmallTypes == TypeSeq!(byte, short)));
}



/**
Removes all occurrences of $(D E) in $(D seq) if any.  Each occurrence is
tested in terms of $(D meta.isSame).

Params:
   E = Compile-time entity to _remove.
 seq = Target sequence.

Returns:
 Sequence $(D seq) in which any occurrence of $(D E) is erased.

Example:
----------
alias meta.remove!(void, int, void, double, void, string) Res;
static assert(is(Res == TypeSeq!(int, double, string)));
----------
 */
template remove(E, seq...)
{
    alias filter!(not!(isSame!E), seq) remove;
}

/// ditto
template remove(alias E, seq...)
{
    alias filter!(not!(isSame!E), seq) remove;
}


unittest
{
    alias remove!(void) empty1;
    alias remove!(1024) empty2;
    static assert(empty1.length == 0);
    static assert(empty2.length == 0);

    static assert([ remove!(void, 1,2,3,2,1) ] == [ 1,2,3,2,1 ]);
    static assert([ remove!(   2, 1,2,3,2,1) ] == [ 1,  3,  1 ]);

    alias remove!(void, int,void,string,void,double) NoVoid;
    alias remove!(   2, int,void,string,void,double) No2;
    static assert(is(NoVoid == Seq!(int,     string,     double)));
    static assert(is(No2    == Seq!(int,void,string,void,double)));
}

unittest
{
    alias meta.remove!(void, int, void, double, void, string) Res;
    static assert(is(Res == TypeSeq!(int, double, string)));
}



/**
Replaces all occurrences of $(D From) in $(D seq) with $(D To).

Params:
 From = Element to remove.
   To = Element to insert in place of $(D From).
  seq = Sequence to perform replacements.

Returns:
 Sequence $(D seq) in which every occurrence of $(D From) (if any) is
 replaced by $(D To).

Example:
----------
struct This;

struct Example(Params...)
{
    // Resolve 'This'
    alias meta.replace!(This, Example!Params, Params) Types;
}
alias Example!(int, double, This) Ex;
static assert(is(Ex.Types[2] == Ex));
----------

Tip:
 You may want to use $(D meta.map) with $(D meta.conditional) to perform more
 complex replacements.  The following example replaces every const types in a
 type sequence with a $(D void).
----------
alias meta.map!(meta.conditional!(q{ is(A == const) }, meta.constant!void),
                int, const double, string, const bool) Res;
static assert(is(Res == TypeSeq!(int, void, string, void)));
----------
 */
template replace(From, To, seq...)
{
    alias map!(conditional!(isSame!From, constant!To), seq) replace;
}

/// ditto
template replace(alias From, To, seq...) if (!isType!From)
{
    alias map!(conditional!(isSame!From, constant!To), seq) replace;
}

/// ditto
template replace(From, alias To, seq...) if (!isType!To)
{
    alias map!(conditional!(isSame!From, constant!To), seq) replace;
}

/// ditto
template replace(alias From, alias To, seq...) if (!isType!From && !isType!To)
{
    alias map!(conditional!(isSame!From, constant!To), seq) replace;
}


unittest
{
    alias replace!(void, int) empty;
    static assert(empty.length == 0);

    alias replace!(void, int, Seq!(int, string, double)) NoMatch;
    static assert(tag!NoMatch == tag!(int, string, double));

    // Test for the specializations
    alias replace!(void, int, Seq!(void, double, void, string)) TT;
    static assert(tag!TT == tag!(int, double, int, string));

    alias replace!(0, int, Seq!(0, 1, 0, -1)) vT;
    static assert(tag!vT == tag!(int, 1, int, -1));

    alias replace!(int, -1, Seq!(int, double, int, string)) Tv;
    static assert(tag!Tv == tag!(-1, double, -1, string));

    alias replace!(null, "", Seq!(null, "abc", null, "def")) vv;
    static assert(tag!vv == tag!("", "abc", "", "def"));

    // Test for ambiguity problem with user-defined types due to @@@BUG4431@@@
    struct S;
    alias replace!(S, int, S, S, S) amb1;
    alias replace!(int, S, S, S, S) amb2;
}

unittest    // doc example
{
    struct This;

    struct Example(Params...)
    {
        alias meta.replace!(This, Example!Params, Params) Types;
    }
    alias Example!(int, double, This) Ex;
    static assert(is(Ex.Types[2] == Ex));
}

unittest    // doc tip
{
    alias meta.map!(meta.conditional!(q{ is(A == const) }, meta.constant!void),
                    int, const double, string, const bool) Res;
    static assert(is(Res == TypeSeq!(int, void, string, void)));
}



/**
Sorts a sequence according to comparison predicate $(D comp).

Params:
 comp = Binary comparison predicate that compares elements of $(D seq).
        It typically works as the $(D <) operator to arrange the result in
        ascending order.
  seq = Sequence to _sort.

Returns:
 Sequence $(D seq) sorted according to the predicate $(D comp).  The relative
 order of equivalent elements will be preserved (i.e. stable).

Example:
----------
// Sort types in terms of the sizes.
alias TypeSeq!(double, int, bool, uint, short) Types;

alias meta.sort!(q{ A.sizeof < B.sizeof }, Types) Inc;
alias meta.sort!(q{ A.sizeof > B.sizeof }, Types) Dec;

static assert(is( Inc == TypeSeq!(bool, short, int, uint, double) ));
static assert(is( Dec == TypeSeq!(double, int, uint, short, bool) ));
----------
 */
template sort(alias comp, seq...)
{
    static if (seq.length < 2)
    {
        alias seq sort;
    }
    else
    {
         alias _sort!(variadicT!comp).Merge!(sort!(comp, seq[ 0  .. $/2]))
                                      .With!(sort!(comp, seq[$/2 ..  $ ])) sort;
    }
}

private template _sort(alias comp)
{
    template Merge()
    {
        template With(B...)
        {
            alias B With;
        }
    }

    template Merge(A...)
    {
        template With()
        {
            alias A With;
        }

        template With(B...)
        {
            // Comparison must be in this order for stability.
            static if (comp!(B[0], A[0]))
            {
                alias Seq!(B[0], Merge!(A        ).With!(B[1 .. $])) With;
            }
            else
            {
                alias Seq!(A[0], Merge!(A[1 .. $]).With!(B        )) With;
            }
        }
    }
}


unittest
{
    struct Scope
    {
        template sizeLess(A, B) { enum sizeLess = (A.sizeof < B.sizeof); }
    }
    alias Scope.sizeLess sizeLess;

    // Trivial cases
    alias sort!(sizeLess) Empty;
    alias sort!(sizeLess, int) Single;
    static assert(is(Empty == Seq!()));
    static assert(is(Single == Seq!(int)));

    //
    alias sort!(sizeLess, int, short) Double;
    static assert(is(Double == Seq!(short, int)));

    alias sort!(sizeLess, long, int, short, byte) Sorted1;
    alias sort!(sizeLess, short, int, byte, long) Sorted2;
    static assert(is(Sorted1 == Seq!(byte, short, int, long)));
    static assert(is(Sorted2 == Seq!(byte, short, int, long)));

    static assert([ sort!(q{ a < b }, 3,5,1,4,2) ] == [ 1,2,3,4,5 ]);
    static assert([ sort!(q{ a > b }, 3,5,1,4,2) ] == [ 5,4,3,2,1 ]);

    // Test for stability
    alias sort!(sizeLess, uint, short, ushort, int) Equiv;
    static assert(is(Equiv == Seq!(short, ushort, uint, int)));
}

unittest    // doc example
{
    alias TypeSeq!(double, int, bool, uint, short) Types;

    alias meta.sort!(q{ A.sizeof < B.sizeof }, Types) Inc;
    alias meta.sort!(q{ A.sizeof > B.sizeof }, Types) Dec;

    static assert(is( Inc == TypeSeq!(bool, short, int, uint, double) ));
    static assert(is( Dec == TypeSeq!(double, int, uint, short, bool) ));
}



/**
Determines if $(D seq) is sorted according to $(D comp).  $(D seq) is sorted
if and only if $(D meta.sort!(comp, seq)) matches $(D seq).

Params:
 comp = Binary comparison template.
  seq = Sequence to examine.

Returns:
 $(D true) iff, for any valid indices $(D i > j), $(D comp!(seq[i], seq[j]))
 evaluates to $(D false).

Example:
 The second sequence in the following example is not sorted since
 $(D ushort.sizeof < int.sizeof) is true.
----------
static assert( meta.isSorted!(q{ A.sizeof < B.sizeof }, byte, short, ushort));
static assert(!meta.isSorted!(q{ A.sizeof < B.sizeof }, byte,   int, ushort));
----------
 */
template isSorted(alias comp, seq...)
{
    static if (seq.length < 2)
    {
        enum isSorted = true;
    }
    else
    {
        // Comparison must be in this order, or false negative happens.
        static if (comp!(seq[$ / 2], seq[$ / 2 - 1]))
        {
            enum isSorted = false;
        }
        else
        {
            // Halving seq reduces the recursion depth.
            enum isSorted = isSorted!(comp, seq[ 0  .. $/2]) &&
                            isSorted!(comp, seq[$/2 ..  $ ]);
        }
    }
}

template isSorted(string comp, seq...)
{
    alias isSorted!(binaryT!comp, seq) isSorted;
}


unittest
{
    struct Scope
    {
        template sizeLess(A, B) { enum sizeLess = (A.sizeof < B.sizeof); }
    }
    alias Scope.sizeLess sizeLess;

    static assert(isSorted!(sizeLess));
    static assert(isSorted!(sizeLess, int));
    static assert(isSorted!(sizeLess, double));

    static assert(isSorted!(sizeLess, short, ushort, int));
    static assert(isSorted!(sizeLess, ushort, short, int));
    static assert(isSorted!(sizeLess, int, uint, float, double));
    static assert(isSorted!(sizeLess, uint, float, int, double));

    static assert(!isSorted!(sizeLess, int, short, double));
    static assert(!isSorted!(sizeLess, int, int, uint, short));
}

unittest
{
    static assert( meta.isSorted!(q{ A.sizeof < B.sizeof }, byte, short, ushort));
    static assert(!meta.isSorted!(q{ A.sizeof < B.sizeof }, byte,   int, ushort));
}



/**
Removes any consecutive group of duplicate elements in $(D seq) except the
first one of each group.  Duplicates are detected with $(D meta.isSame).

Params:
 seq = Target sequence.

Returns:
 $(D seq) without any consecutive duplicate elements.

Example:
----------
alias meta.uniq!(1, 2, 3, 3, 4, 4, 4, 2, 2) result;
static assert([ result ] == [ 1, 2, 3, 4, 2 ]);
----------
 */
template uniq(seq...)
{
    alias uniqBy!(isSame, seq) uniq;
}


unittest
{
    alias uniq!() empty;
    static assert(empty.length == 0);

    alias uniq!(int) Single;
    static assert(is(Single == Seq!(int)));

    alias uniq!(int, double, string) Nodup;
    static assert(is(Nodup == Seq!(int, double, string)));

    alias uniq!(int, int, double, string, string, string) Dup;
    static assert(is(Dup == Seq!(int, double, string)));

    alias uniq!("abc", "123", "abc", "123") noConsec;
    static assert([ noConsec ] == [ "abc", "123", "abc", "123" ]);
}

unittest
{
    alias meta.uniq!(1, 2, 3, 3, 4, 4, 4, 2, 2) result;
    static assert([ result ] == [ 1, 2, 3, 4, 2 ]);
}



/**
Generalization of $(D meta.uniq) detecting duplicates with $(D eq), instead
of $(D meta.isSame).

Params:
  eq = Binary predicate template that determines if passed-in arguments are
       the same (or duplicated).
 seq = Target sequence.

Returns:
 Sequence $(D seq) in which any consecutive group of duplicate elements are
 squeezed into the fist one of each group.

Example:
----------
alias meta.uniqBy!(q{ A.sizeof == B.sizeof },
                   int, uint, short, ushort, uint) Res;
static assert(is(Res == TypeSeq!(int, short, uint)));
----------
 */
template uniqBy(alias eq, seq...)
{
    alias mapRec!(_uniqCons!(binaryT!eq).uniqCons, seq) uniqBy;
}


private template _uniqCons(alias eq)
{
    template uniqCons(car, cdr...)
    {
        static if (cdr.length && eq!(car, cdr[0]))
        {
            alias Seq!(car, cdr[1 .. $]) uniqCons;
        }
        else
        {
            alias Seq!(car, cdr) uniqCons;
        }
    }

    template uniqCons(alias car, cdr...)
    {
        static if (cdr.length && eq!(car, cdr[0]))
        {
            alias Seq!(car, cdr[1 .. $]) uniqCons;
        }
        else
        {
            alias Seq!(car, cdr) uniqCons;
        }
    }
}


unittest
{
    alias uniqBy!(q{ a == b }) empty;
    static assert(empty.length == 0);

    alias uniqBy!(q{ a == b }, 1,2,3,4,5) nodup;
    static assert([ nodup ] == [ 1,2,3,4,5 ]);

    alias uniqBy!(q{ a < b }, 1,2,3,0,8,7,6,5) noinc;
    static assert([ noinc ] == [ 1,0,7,6,5 ]);
}

unittest
{
    alias meta.uniqBy!(q{ A.sizeof == B.sizeof },
                       int, uint, short, ushort, uint) Res;
    static assert(is(Res == TypeSeq!(int, short, uint)));
}



/**
Completely removes all duplicate elements in $(D seq) except the first one.
Duplicates are detected with $(D meta.isSame).

Params:
 seq = Target sequence.

Returns:
 Sequence $(D seq) without any duplicate elements.

Example:
----------
alias meta.removeDuplicates!(int, bool, bool, int, string) Res;
static assert(is(Res == TypeSeq!(int, bool, string)));
----------
 */
template removeDuplicates(seq...)
{
    alias removeDuplicatesBy!(isSame, seq) removeDuplicates;
}


unittest
{
    alias removeDuplicates!() empty;
    static assert(empty.length == 0);

    alias removeDuplicates!(int) Single;
    static assert(is(Single == Seq!(int)));

    alias removeDuplicates!(int, double, string, int, double) Dup;
    static assert(is(Dup == Seq!(int, double, string)));

    alias removeDuplicates!("fun", "gun", "fun", "hun") values;
    static assert([ values ] == [ "fun", "gun", "hun" ]);
}

unittest
{
    alias meta.removeDuplicates!(int, bool, bool, int, string) Res;
    static assert(is(Res == TypeSeq!(int, bool, string)));
}



/**
Generalization of $(D meta.removeDuplicates) detecting duplicates with
$(D eq), instead of $(D meta.isSame).

Params:
  eq = Binary predicate template that determines if passed-in arguments are
       the same (or duplicated).
 seq = Target sequence.

Returns:
 Sequence $(D seq) in which any group of duplicate elements are eliminated
 except the fist one of each group.

Example:
----------
alias meta.removeDuplicatesBy!(q{ A.sizeof == B.sizeof },
                               int, uint, short, ushort, uint) Res;
static assert(is(Res == TypeSeq!(int, short)));
----------
 */
template removeDuplicatesBy(alias eq, seq...)
{
    static if (seq.length < 2)
    {
        alias seq removeDuplicatesBy;
    }
    else
    {
        alias Seq!(seq[0],
                   removeDuplicatesBy!(
                       eq, filter!(bind!(not!eq, seq[0]), seq[1 .. $])))
              removeDuplicatesBy;
    }
}


unittest
{
    alias removeDuplicatesBy!(q{ a == b }) empty;
    static assert(empty.length == 0);

    alias removeDuplicatesBy!(q{ a == b }, 1,2,3,4,5) nodup;
    static assert([ nodup ] == [ 1,2,3,4,5 ]);

    alias removeDuplicatesBy!(q{ a < b }, 9,6,7,8,3,4,5,0) decrease;
    static assert([ decrease ] == [ 9,6,3,0 ]);
}

unittest
{
    alias meta.removeDuplicatesBy!(q{ A.sizeof == B.sizeof },
                                   int, uint, short, ushort, uint) Res;
    static assert(is(Res == TypeSeq!(int, short)));
}



//----------------------------------------------------------------------------//
// Iteration & Query
//----------------------------------------------------------------------------//


/**
Reduces the sequence $(D seq) by successively applying a binary template
$(D fun) over elements, with an initial state $(D Seed):
----------
fun!( ... fun!(fun!(Seed, seq[0]), seq[1]) ..., seq[$ - 1])
----------

Params:
  fun = Binary template or string.
 Seed = The initial state.
  seq = Sequence of zero or more compile-time entities to _reduce.

Returns:
 The last result of $(D fun), or $(D Seed) if $(D seq) is empty.

Example:
 Computing the net accumulation of the size of types.
----------
alias TypeSeq!(int, double, short, bool, dchar) Types;

// Note: 'a' gets the "current sum" and 'B' gets a type in the sequence.
enum size = meta.reduce!(q{ a + B.sizeof }, 0, Types);
static assert(size == 4 + 8 + 2 + 1 + 4);
----------

See_Also:
 $(D meta.scan): reduce with history.
 */
template reduce(alias fun, Seed, seq...)
{
    alias _reduce!(binaryT!fun).reduce!(Seed, seq) reduce;
}

/// ditto
template reduce(alias fun, alias Seed, seq...)
{
    alias _reduce!(binaryT!fun).reduce!(Seed, seq) reduce;
}


private template _reduce(alias fun)
{
    template reduce(      Seed) { alias Seed reduce; }
    template reduce(alias Seed) { alias Seed reduce; }
    template reduce(      Seed, seq...) { mixin(_reduceBody); }
    template reduce(alias Seed, seq...) { mixin(_reduceBody); }

    enum _reduceBody =
    q{
        static if (seq.length == 1)
        {
            alias fun!(Seed, seq[0]) reduce;
        }
        else
        {
            // Halving seq reduces the recursion depth.
            alias reduce!(reduce!(Seed, seq[0 .. $/2]), seq[$/2 .. $]) reduce;
        }
    };
}


unittest
{
    static assert(is(reduce!(q{ A[B] }, int) == int));
    static assert(reduce!(q{ a ~ b }, "abc") == "abc");

    alias reduce!(q{ A[B] }, int, double, string) Assoc;
    static assert(is(Assoc == int[double][string]));

    enum concat = reduce!(q{ a ~ b }, "abc", "123", "xyz", "987");
    static assert(concat == "abc123xyz987");

    // Test for ambiguity on matching string/alias parameters
    struct S {}
    alias reduce!(        q{ A[B] }, S) K1;
    alias reduce!(binaryT!q{ A[B] }, S) K2;
    enum s1 = reduce!(        q{ a ~ b }, "");
    enum s2 = reduce!(binaryT!q{ a ~ b }, "");
}

unittest    // doc example
{
    alias TypeSeq!(int, double, short, bool, dchar) Types;

    enum size = meta.reduce!(q{ a + B.sizeof }, 0, Types);
    static assert(size == 4 + 8 + 2 + 1 + 4);
}



/**
Returns a sequence generated by successively applying a binary template
$(D fun) over the elements of $(D seq), with an initial state $(D Seed):
----------
scan[0] = Seed;
scan[1] = fun!(scan[0], seq[0]);
scan[2] = fun!(scan[1], seq[1]);
        :
----------
Note that $(D scan[i]) is equal to $(D meta.reduce!(fun, Seed, seq[0 .. i])).

Params:
  fun = Binary template or string.
 Seed = The initial state.
  seq = Sequence of zero or more compile-time entities to _scan.

Returns:
 Sequence of the results of $(D fun) preceded by $(D Seed).

Example:
 Computing the sum of the size of types with history.
----------
alias TypeSeq!(int, double, short, bool, dchar) Types;

alias meta.scan!(q{ a + B.sizeof }, 0, Types) sums;
static assert([ sums ] == [ 0,
                            0+4,
                            0+4+8,
                            0+4+8+2,
                            0+4+8+2+1,
                            0+4+8+2+1+4 ]);
----------
 Note that $(D sums[5]), or $(D sums[Types.length]), equals the result
 of the corresponding example of $(D meta.reduce).
 */
template scan(alias fun, Seed, seq...)
{
    alias _scan!(binaryT!fun).scan!(Seed, seq) scan;
}

/// ditto
template scan(alias fun, alias Seed, seq...)
{
    alias _scan!(binaryT!fun).scan!(Seed, seq) scan;
}


private template _scan(alias fun)
{
    template scan(      Seed, seq...) { mixin(_scanBody); }
    template scan(alias Seed, seq...) { mixin(_scanBody); }

    enum _scanBody =
    q{
        static if (seq.length == 0)
        {
            alias Seq!(Seed) scan;
        }
        else
        {
            alias Seq!(Seed, scan!(fun!(Seed, seq[0]), seq[1 .. $])) scan;
        }
    };
}


unittest
{
    alias scan!(q{ A[B] }, int, double, string) Assocs;
    static assert(Assocs.length == 3);
    static assert(is(Assocs[0] == int));
    static assert(is(Assocs[1] == int[double]));
    static assert(is(Assocs[2] == int[double][string]));

    alias scan!(q{ a ~ b }, "abc", "123", "xyz", "987") concats;
    static assert(concats.length == 4);
    static assert(concats[0] == "abc");
    static assert(concats[1] == "abc123");
    static assert(concats[2] == "abc123xyz");
    static assert(concats[3] == "abc123xyz987");

    // Test for non-ambiguity
    struct S {}
    alias scan!(        q{ A[B] }, S) K1;
    alias scan!(binaryT!q{ A[B] }, S) K2;
    enum s1 = scan!(        q{ a ~ b }, "");
    enum s2 = scan!(binaryT!q{ a ~ b }, "");
}

unittest    // doc example
{
    alias TypeSeq!(int, double, short, bool, dchar) Types;

    alias meta.scan!(q{ a + B.sizeof }, 0, Types) sums;
    static assert([ sums ] == [ 0,
                                0+4,
                                0+4+8,
                                0+4+8+2,
                                0+4+8+2+1,
                                0+4+8+2+1+4 ]);
}



/**
Looks for the first "top" element of a sequence in terms of the specified
comparison template $(D comp).  This template is effectively the same
as $(D meta.sort!(comp, seq)[0]).

Params:
 comp = Binary template or expression string that compares items in
        the sequence for an ordering.
  seq = One or more compile-time entities.

Example:
 To get the largest element in the sequence, specify a greater-than operator
 as the $(D comp) argument.
----------
alias TypeSeq!(int, bool, double, short) Types;

// Take the largest type in the sequence: double.
alias meta.most!(q{ A.sizeof > B.sizeof }, Types) Largest;
static assert(is(Largest == double));
----------
 */
template most(alias comp, seq...) if (seq.length > 0)
{
    alias reduce!(_more!(binaryT!comp), seq) most;
}


private template _more(alias comp)
{
    template _more(pair...)
    {
        // Comparison must be in this order for stability.
        static if (comp!(pair[1], pair[0]))
        {
            alias Id!(pair[1]) _more;
        }
        else
        {
            alias Id!(pair[0]) _more;
        }
    }
}


unittest
{
    static assert(most!(q{ a < b }, 5) == 5);
    static assert(most!(q{ a < b }, 5, 5, 5) == 5);
    static assert(most!(q{ a < b }, 5, 1, -3, 2, 4) == -3);

    // stability
    alias most!(q{ A.sizeof < B.sizeof }, short, byte, float, ubyte, uint) Min;
    alias most!(q{ A.sizeof > B.sizeof }, short, byte, float, ubyte, uint) Max;
    static assert(is(Min ==  byte));
    static assert(is(Max == float));
}

unittest    // doc example
{
    alias TypeSeq!(int, bool, double, short) Types;

    alias meta.most!(q{ A.sizeof > B.sizeof }, Types) Largest;
    static assert(is(Largest == double));
}



/*
Groundwork for find-family algorithms.  index!() finds the index of the
first m-subsequence satisfying the predicate.  The predicate is evaluated
lazily so that unnecessary instantiations should not kick in.

Params:
 pred = m-ary predicate template.
    m = Size of chunk to find.
 */
template _findChunk(alias pred, size_t m)
{
    template index(seq...) if (seq.length < m)
    {
        enum index = seq.length;    // not found
    }

    // Simple search.
    template index(seq...) if (m <= seq.length && seq.length < 2*m)
    {
        static if (pred!(seq[0 .. m]))
        {
            enum size_t index = 0;
        }
        else
        {
            enum size_t index = index!(seq[1 .. $]) + 1;
        }
    }

    // Halve seq to reduce the recursion depth.  This specialization
    // is just for that purpose and index!() could work without this.
    template index(seq...) if (2*m <= seq.length)
    {
        static if (index!(seq[0 .. $/2 + m - 1]) < seq.length/2)
        {
            enum index = index!(seq[0 .. $/2 + m - 1]);
        }
        else
        {
            enum index = index!(seq[$/2 .. $]) + seq.length/2;
        }
    }
}



/**
Looks for the first occurrence of $(D E) in $(D seq).

Params:
   E = Compile-time entity to look for.
 seq = Target sequence.

Returns:
 Subsequence of $(D seq) after $(D E) (inclusive).  The empty sequence
 is returned if $(D E) is not found.

Example:
----------
alias TypeSeq!(int, short, double, bool, string) Types;

alias meta.find!(bool, Types) AfterBool;
static assert(is(AfterBool == TypeSeq!(bool, string)));

// Take the subsequence after the largest type.
alias meta.find!(meta.most!(q{ A.sizeof > B.sizeof }, Types),
                 Types) Sub;
static assert(is(Sub == TypeSeq!(double, bool, string)));
----------
 */
template find(E, seq...)
{
    alias findIf!(isSame!E, seq) find;
}

/// ditto
template find(alias E, seq...)
{
    alias findIf!(isSame!E, seq) find;
}


unittest
{
    static assert(find!(void).length == 0);
    static assert(find!(   0).length == 0);

    static assert(find!(void, int, string).length == 0);
    static assert(find!(   0, int, string).length == 0);

    alias find!(void, int, string, void, void, double) Void;
    static assert(is(Void == Seq!(void, void, double)));

    alias find!("opAssign", "toString", "opAssign", "empty") opAss;
    static assert([ opAss ] == [ "opAssign", "empty" ]);
}

unittest
{
    alias TypeSeq!(int, short, double, bool, string) Types;

    alias meta.find!(bool, Types) AfterBool;
    static assert(is(AfterBool == TypeSeq!(bool, string)));

    alias meta.find!(meta.most!(q{ A.sizeof > B.sizeof }, Types),
                     Types) Sub;
    static assert(is(Sub == TypeSeq!(double, bool, string)));
}



/**
Looks for the first element of $(D seq) satisfying $(D pred).

Params:
 pred = Unary predicate template.
  seq = Target sequence.

Returns:
 Subsequence of $(D seq) after the found element, if any, inclusive.
 The empty sequence is returned if not found.

Example:
----------
alias meta.findIf!(q{ is(A == const) },
                   int, double, const string, bool) Res;
static assert(is(Res == TypeSeq!(const string, bool)));
----------
 */
template findIf(alias pred, seq...)
{
    alias seq[_findChunk!(unaryT!pred, 1).index!seq .. $] findIf;
}


unittest
{
    static assert(findIf!(q{ true }).length == 0);

    static assert([ findIf!(q{ a < 0 }, 5,4,3,2,1,0) ] == []);
    static assert([ findIf!(q{ a < 0 }, 2,1,0,-1,-2) ] == [ -1,-2 ]);
}

unittest
{
    alias meta.findIf!(q{ is(A == const) },
                       int, double, const string, bool) Res;
    static assert(is(Res == TypeSeq!(const string, bool)));
}



/**
Takes a subsequence of $(D seq) until encountering $(D E).

Params:
   E = Compile-time entity to look for.
 seq = Target sequence.

Returns:
 Subsequence of $(D seq) before $(D E) (exclusive).  The passed-in sequence
 $(D seq) is returned if $(D E) is not found.

Example:
----------
alias meta.until!(void, int, double, void, string) Res;
static assert(is(Res == TypeSeq!(int, double)));
----------
 */
template until(E, seq...)
{
    alias untilIf!(isSame!E, seq) until;
}

/// ditto
template until(alias E, seq...)
{
    alias untilIf!(isSame!E, seq) until;
}


unittest
{
    static assert(until!(void).length == 0);
    static assert(until!(   0).length == 0);

    static assert(is(until!(void, int, double) == Seq!(int, double)));
    static assert(is(until!(   0, int, double) == Seq!(int, double)));

    alias until!(void, int, string, void, void, double) Void;
    static assert(is(Void == Seq!(int, string)));

    alias until!("opAssign", "toString", "opAssign", "empty") opAss;
    static assert([ opAss ] == [ "toString" ]);
}

unittest
{
    alias meta.until!(void, int, double, void, string) Res;
    static assert(is(Res == TypeSeq!(int, double)));
}



/**
Slices sequence $(D seq) until encoutering an element satisfying $(D pred).

Params:
 pred = Unary predicate template.
  seq = Target sequence.

Returns:
 Subsequence of $(D seq) before the found element, if any, exclusive.
 The passed-in sequence $(D seq) is returned if not found.

Example:
----------
alias meta.untilIf!(q{ is(A == const) },
                    int, double, const string, bool) Res;
static assert(is(Res == TypeSeq!(int, double)));
----------
 */
template untilIf(alias pred, seq...)
{
    alias seq[0 .. _findChunk!(unaryT!pred, 1).index!seq] untilIf;
}


unittest
{
    static assert(untilIf!(q{ true }).length == 0);

    static assert([ untilIf!(q{ a < 0 }, 5,4,3,2,1,0) ] == [ 5,4,3,2,1,0 ]);
    static assert([ untilIf!(q{ a < 0 }, 2,1,0,-1,-2) ] == [ 2,1,0 ]);
    static assert([ untilIf!(q{ a < 0 }, -1,-2,-3,-4) ] == []);
}

unittest
{
    alias meta.untilIf!(q{ is(A == const) },
                        int, double, const string, bool) Res;
    static assert(is(Res == TypeSeq!(int, double)));
}



/**
Finds the index of the first occurrence of $(D E) in a sequence.

Params:
   E = Compile-time entity to look for.
 seq = Target sequence.

Returns:
 Index of the first element, if any, that is same as $(D E).  $(D -1) is
 returned if not found.  The type of the result is $(D sizediff_t).

Example:
----------
alias TypeSeq!(int, double, bool, string) Types;

static assert(meta.index!(bool, Types) ==  2);
static assert(meta.index!(void, Types) == -1);
----------
 */
template index(E, seq...)
{
    enum index = indexIf!(isSame!E, seq);
}

/// ditto
template index(alias E, seq...)
{
    enum index = indexIf!(isSame!E, seq);
}


unittest
{
    static assert(index!(int) == -1);
    static assert(index!( 16) == -1);

    static assert(index!(int, string, double, bool) == -1);
    static assert(index!( 16, string, double, bool) == -1);

    static assert(index!(string, string, double, int) == 0);
    static assert(index!(double, string, double, int) == 1);
    static assert(index!(   int, string, double, int) == 2);

    static assert(index!( 4, 4, 8, 16) == 0);
    static assert(index!( 8, 4, 8, 16) == 1);
    static assert(index!(16, 4, 8, 16) == 2);

    // Type check
    static assert(is(typeof(index!(int, int, double)) == sizediff_t));
    static assert(is(typeof(index!( 16, int, double)) == sizediff_t));
}

unittest
{
    alias TypeSeq!(int, double, bool, string) Types;

    static assert(meta.index!(bool, Types) ==  2);
    static assert(meta.index!(void, Types) == -1);
}



/**
Finds the index of the first element of a sequence satisfying a predicate.

Params:
 pred = Unary predicate template.
  seq = Target sequence.

Returns:
 Index of the first element, if any, satisfying the predicate $(D pred).
 $(D -1) is returned if not found.  The type of the result is $(D sizediff_t).

Example:
----------
alias TypeSeq!(int, double, short, string) Types;

static assert(meta.indexIf!(q{ A.sizeof < 4 }, Types) ==  2);
static assert(meta.indexIf!(q{ A.sizeof < 2 }, Types) == -1);
----------
 */
template indexIf(alias pred, seq...)
{
    static if (untilIf!(pred, seq).length == seq.length)
    {
        enum sizediff_t indexIf = -1;
    }
    else
    {
        enum sizediff_t indexIf = untilIf!(pred, seq).length;
    }
}


unittest
{
    static assert(indexIf!(q{  true }) == -1);
    static assert(indexIf!(q{ false }, string, double, bool) == -1);

    static assert(indexIf!(q{ a % 2 == 0 }, 2, 6, 8) == 0);
    static assert(indexIf!(q{ a % 3 == 0 }, 2, 6, 8) == 1);
    static assert(indexIf!(q{ a % 4 == 0 }, 2, 6, 8) == 2);

    // Type check
    static assert(is(typeof(indexIf!(q{  true }, int, double)) == sizediff_t));
    static assert(is(typeof(indexIf!(q{ false }, int, double)) == sizediff_t));
}

unittest
{
    alias TypeSeq!(int, double, short, string) Types;

    static assert(meta.indexIf!(q{ A.sizeof < 4 }, Types) ==  2);
    static assert(meta.indexIf!(q{ A.sizeof < 2 }, Types) == -1);
}



/**
Counts the number of occurrences of $(D E) in $(D seq).

Params:
   E = Compile-time entity to look for.
 seq = Target sequence.

Returns:
 The number of elements in $(D seq) satisfying $(D isSame!E).

Example:
----------
alias TypeSeq!(int, double, string, void) Types;
static assert(meta.count!(void, Types) == 1);
----------
 */
template count(E, seq...)
{
    enum count = countIf!(isSame!E, seq);
}

/// ditto
template count(alias E, seq...)
{
    enum count = countIf!(isSame!E, seq);
}


unittest
{
    static assert(count!(int) == 0);
    static assert(count!( 16) == 0);

    static assert(count!(int, double, string, bool) == 0);
    static assert(count!( 16, double, string, bool) == 0);

    static assert(count!(int, int, void, void) == 1);
    static assert(count!(int, int,  int, void) == 2);
    static assert(count!(int, int,  int,  int) == 3);

    static assert(count!(16, 16,  8,  4) == 1);
    static assert(count!(16, 16, 16,  4) == 2);
    static assert(count!(16, 16, 16, 16) == 3);
}

unittest
{
    alias TypeSeq!(int, double, string, void) Types;
    static assert(meta.count!(void, Types) == 1);
}



/**
Counts the number of elements in $(D seq) satisfying the predicate $(D pred).

Params:
 pred = Unary predicate template.
  seq = Target sequence.

Returns:
 The number of elements in $(D seq) satisfying the predicate $(D pred).

Example:
----------
static assert(meta.countIf!(q{ a[0] == '_' },
                            "__ctor", "__dtor", "foo", "bar") == 2);
----------
 */
template countIf(alias pred, seq...)
{
    static if (seq.length < 2)
    {
        static if (seq.length == 0 || !pred!(seq[0]))
        {
            enum size_t countIf = 0;
        }
        else
        {
            enum size_t countIf = 1;
        }
    }
    else
    {
        // Halving seq reduces the recursion depth.
        enum countIf = countIf!(pred, seq[ 0  .. $/2]) +
                       countIf!(pred, seq[$/2 ..  $ ]);
    }
}

template countIf(string pred, seq...)
{
    enum countIf = countIf!(unaryT!pred, seq);
}


unittest
{
    static assert(countIf!(q{  true }) == 0);
    static assert(countIf!(q{ false }, int, double, string) == 0);

    static assert(countIf!(q{ a % 6 == 0 }, 1,2,3,4,5,6) == 1);
    static assert(countIf!(q{ a % 3 == 0 }, 1,2,3,4,5,6) == 2);
    static assert(countIf!(q{ a % 2 == 0 }, 1,2,3,4,5,6) == 3);
}

unittest
{
    static assert(meta.countIf!(q{ a[0] == '_' },
                                "__ctor", "__dtor", "foo", "bar") == 2);
}



/**
Determines if, respectively, _all/_any/_none of the elements in a
sequence $(D seq) satisfies the predicate $(D pred).  Specifically:
----------
 all =  pred!(seq[0]) &&  pred!(seq[1]) && ... ;
 any =  pred!(seq[0]) ||  pred!(seq[1]) || ... ;
none = !pred!(seq[0]) && !pred!(seq[1]) && ... ;
----------

These templates evaluate conditions lazily just like usual boolean
expressions, so unnecessary instantiations will never kick in.  For
example, $(D meta.all) immediately returns $(D false) at first failing
element (if any) and doesn't instantiate $(D pred) with remaining
elements.

Params:
 pred = Unary predicate template or expression string.
  seq = Zero or more compile-time entities to examine.

Returns:
 $(D true) if _all/_any/_none of the elements of the sequence satisfies
 the predicate.  For the empty sequence, $(D meta.all) and $(D meta.none)
 returns $(D true); and $(D meta.any) returns $(D false).

Example:
 These templates would be useful in template constraints:
----------
import std.meta, std.range, std.typecons;

// This function requires all arguments should be input ranges.
auto dropFront(Ranges...)(ref Ranges ranges)
    if (meta.all!(isInputRange, Ranges))
{
    Tuple!(meta.map!(ElementType, Ranges)) result;

    foreach (i, R; Ranges)
    {
        result[i] = ranges[i].front;
        ranges[i].popFront();
    }
    return result;
}
----------
 */
template all(alias pred, seq...)
{
    enum all = (_findChunk!(not!pred, 1).index!seq == seq.length);
}


unittest
{
    struct Scope
    {
        template isZero(int n) { enum isZero = (n == 0); }
    }
    alias Scope.isZero isZero;

    static assert( all!(isZero));
    static assert( all!(isZero, 0));
    static assert(!all!(isZero, 1));
    static assert(!all!(isZero, 1, 2));
    static assert(!all!(isZero, 0, 1, 2));
    static assert( all!(isZero, 0, 0, 0));

    // Laziness
    static assert(!all!(isZero, 1, int));
    static assert(!all!(isZero, 0, 1, int));
    static assert(!all!(isZero, 0, 0, 1, int));
    static assert(!all!(isZero, 0, 0, 0, 1, int));

    // String
    static assert(all!(q{ is(A == const) }));
    static assert(all!(q{ is(A == const) }, const int));
}


/** ditto */
template any(alias pred, seq...)
{
    enum any = (_findChunk!(unaryT!pred, 1).index!seq < seq.length);
}


unittest
{
    struct Scope
    {
        template isZero(int n) { enum isZero = (n == 0); }
    }
    alias Scope.isZero isZero;

    static assert(!any!(isZero));
    static assert( any!(isZero, 0));
    static assert(!any!(isZero, 1));
    static assert(!any!(isZero, 1, 2));
    static assert( any!(isZero, 0, 1, 2));
    static assert( any!(isZero, 0, 0, 0));

    // Laziness
    static assert(any!(isZero, 0, int));
    static assert(any!(isZero, 1, 0, int));
    static assert(any!(isZero, 1, 2, 0, int));
    static assert(any!(isZero, 1, 2, 3, 0, int));

    // String
    static assert(!any!(q{ is(A == const) }));
    static assert( any!(q{ is(A == const) }, const int));
}


/** ditto */
template none(alias pred, seq...)
{
    enum none = (_findChunk!(unaryT!pred, 1).index!seq == seq.length);
}


unittest
{
    struct Scope
    {
        template isZero(int n) { enum isZero = (n == 0); }
    }
    alias Scope.isZero isZero;

    static assert( none!(isZero));
    static assert(!none!(isZero, 0));
    static assert( none!(isZero, 1));
    static assert( none!(isZero, 1, 2));
    static assert(!none!(isZero, 0, 1, 2));
    static assert(!none!(isZero, 0, 0, 0));

    // Laziness
    static assert(!none!(isZero, 0, int));
    static assert(!none!(isZero, 1, 0, int));
    static assert(!none!(isZero, 1, 2, 0, int));
    static assert(!none!(isZero, 1, 2, 3, 0, int));

    // String
    static assert( none!(q{ is(A == const) }));
    static assert(!none!(q{ is(A == const) }, const int));
}



/**
Determines if _only one of the elements of $(D seq) satisfies the predicate
$(D pred).  The predicate is tested for all the elements.

Params:
 pred = Unary predicate template or expression string.
  seq = Zero or more compile-time entities to examine.

Returns:
 $(D true) if $(D seq) is not empty and _only one of the elements satisfies
 the predicate.  Otherwise, $(D false) is returned.

Example:
----------
// Allow only one class in a base class list.
template isValidBase(Bases...)
{
    enum isValidBase = meta.only!(q{ is(A == class) }, Bases);
}

class B {}
class C {}
interface I {}
interface J {}
static assert( isValidBase!(B, I, J));
static assert(!isValidBase!(B, I, C));
----------
 */
template only(alias pred, seq...)
{
    enum only = (countIf!(pred, seq) == 1);
}


unittest
{
    struct Scope
    {
        template isZero(int n) { enum isZero = (n == 0); }
    }
    alias Scope.isZero isZero;

    static assert(!only!(isZero));
    static assert( only!(isZero, 0));
    static assert(!only!(isZero, 1));
    static assert(!only!(isZero, 1, 2));
    static assert( only!(isZero, 0, 1, 2));
    static assert(!only!(isZero, 0, 0, 0));

    // String
    static assert(!only!(q{ is(A == const) }));
    static assert( only!(q{ is(A == const) }, const int));
}

unittest    // doc example
{
    struct Scope
    {
        template isValidBase(Bases...)
        {
            enum isValidBase = meta.only!(q{ is(A == class) }, Bases);
        }
    }
    alias Scope.isValidBase isValidBase;

    class B {}
    class C {}
    interface I {}
    interface J {}
    static assert( isValidBase!(B, I, J));
    static assert(!isValidBase!(B, I, C));
}



//----------------------------------------------------------------------------//
// Set Operations
//----------------------------------------------------------------------------//


/**
Normalizes the order of elements of a given sequence.  The normalization
would be useful for comparing sequences with respect only to their contents
independent of the order.

Params:
 seq = Any sequence to canonicalize the order.

Returns:
 Sequence $(D seq) rearranged in a uniform order.  Duplicate elements will
 be grouped into a continuous repetition of that entity.

Example:
----------
alias meta.setify!(int, bool, double, int) A;
alias meta.setify!(bool, bool, double, int) B;

static assert(is(A == TypeSeq!(bool, double, int, int)));
static assert(is(B == TypeSeq!(bool, bool, double, int)));

static assert(is(meta.uniq!A == meta.uniq!B));
----------
 */
template setify(seq...)
{
    alias sort!(metaComp, seq) setify;
}


unittest
{
    alias meta.setify!(int, bool, double, int) A;
    alias meta.setify!(bool, bool, double, int) B;

    static assert(is(A == TypeSeq!(bool, double, int, int)));
    static assert(is(B == TypeSeq!(bool, bool, double, int)));

    static assert(is(meta.uniq!A == meta.uniq!B));
}



/**
Determines if all the specified items present in a sequence.

Params:
   set = The sequence, packed with $(D meta.pack), to test.
 items = Zero or more compile-time entities to test the presence of.

         The number of duplicates, if any, is significant.  If there are
         $(D m) repetitions of an entity in $(D items), the template checks
         if $(D sub) _contains $(D m) or more duplicates of that entity; and
         returns $(D false) if not.

Returns:
 $(D true) if the sequence $(D set.expand) _contains all the _items in
 $(D items) including duplicates, or $(D false) if not.  $(D true) is
 returned if $(D items) is empty.

Example:
----------
alias TypeSeq!(string, int, int, double) A;
static assert( meta.contains!(meta.pack!A, string));
static assert( meta.contains!(meta.pack!A, double, int, int));
static assert(!meta.contains!(meta.pack!A, double, double));
static assert(!meta.contains!(meta.pack!A, void));
----------
 */
template contains(alias set, items...)
{
    enum contains = (intersection!(set, pack!items).length == items.length);
}


unittest
{
    static assert( contains!(pack!()));
    static assert(!contains!(pack!(), int));
    static assert(!contains!(pack!(), int, "index"));

    alias pack!(1, 1, 1, 2, 2, 3) nums;
    static assert(contains!(nums));
    static assert(contains!(nums, nums.expand));

    static assert(contains!(nums, 3));
    static assert(contains!(nums, 1, 2, 3));
    static assert(contains!(nums, 3, 1, 2));
    static assert(contains!(nums, 1, 1, 2, 2));
    static assert(contains!(nums, 3, 1, 1, 1));

    static assert(!contains!(nums, 0));
    static assert(!contains!(nums, 0, 1, 2, 3));
    static assert(!contains!(nums, 1, 1, 1, 1));
    static assert(!contains!(nums, 3, 3));
}

unittest
{
    alias TypeSeq!(string, int, int, double) A;
    static assert( meta.contains!(meta.pack!A, string));
    static assert( meta.contains!(meta.pack!A, double, int, int));
    static assert(!meta.contains!(meta.pack!A, double, double));
    static assert(!meta.contains!(meta.pack!A, void));
}



/* used by unittests */
template isSameSet(alias A, alias B)
{
    enum isSameSet = is(pack!(setify!(A.expand)).Tag ==
                        pack!(setify!(B.expand)).Tag);
}

template isSameSet(alias A)
{
    template isSameSet(alias B)
    {
        alias .isSameSet!(A, B) isSameSet;
    }
}



/**
Takes the _intersection of zero or more sequences.

Params:
 seqs = Sequence of sequences to take _intersection of.  Each sequence must
        be packed into $(D meta.pack) or a compatible entity.

Returns:
 Sequence composed only of common elements of all the given sequences.  The
 empty sequence is returned if no sequence is passed, i.e. $(D seqs) is empty.

 If the sequences contain $(D m1,m2,...) duplicates of the same entity
 respectively, the resulting _intersection will contain $(D min(m1,m2,...)),
 or the least, duplicates of that entity.

Example:
----------
alias meta.intersection!(meta.pack!(int, int, double, bool, bool),
                         meta.pack!(int, double, bool, double, bool),
                         meta.pack!(bool, string, int, int, bool)) Inter;
static assert(is(Inter == TypeSeq!(bool, bool, int)));
----------
 */
template intersection(seqs...)
{
    static if (seqs.length == 0)
    {
        alias Seq!() intersection;
    }
    else
    {
        alias reduce!(compose!(pack, .intersection), seqs).expand intersection;
    }
}

template intersection(alias A, alias B)
{
    alias intersectionBy!(metaComp, A, B) intersection;
}


unittest
{
    // Test for values
    alias Seq!(1,2,2,4,5,7,9) a;
    alias Seq!(0,1,2,4,4,7,8) b;
    alias Seq!(0,1,4,4,5,7,8) c;

    alias intersection!(pack!a, pack!a) aa;
    alias intersection!(pack!a, pack!b) ab;
    alias intersection!(pack!b, pack!c) bc;
    static assert(isSameSet!( pack!aa, pack!(a) ));
    static assert(isSameSet!( pack!ab, pack!(1,2,4,7) ));
    static assert(isSameSet!( pack!bc, pack!(0,1,4,4,7,8) ));

    // Test for types
    alias Seq!(int, int, double, string) T;
    alias Seq!(double, string, double, int) U;
    alias Seq!(double, void, int, double) V;

    alias intersection!(pack!T, pack!T) TT;
    alias intersection!(pack!T, pack!U) TU;
    alias intersection!(pack!U, pack!V) UV;
    static assert(isSameSet!( pack!TT, pack!(T) ));
    static assert(isSameSet!( pack!TU, pack!(double, int, string) ));
    static assert(isSameSet!( pack!UV, pack!(double, double, int) ));

    // Degeneration
    alias Seq!() e;
    static assert(intersection!(pack!e, pack!e).length == 0);
    static assert(intersection!(pack!e, pack!T).length == 0);
    static assert(intersection!(pack!T, pack!a).length == 0);
}

unittest
{
    static assert(intersection!().length == 0);

    alias intersection!(pack!()) Empty;
    alias intersection!(pack!(int, double, string)) Single;
    static assert(is(Empty == TypeSeq!()));
    static assert(is(Single == TypeSeq!(int, double, string)));
}

unittest
{
    alias meta.intersection!(meta.pack!(int, int, double, bool, bool),
                             meta.pack!(int, double, bool, double, bool),
                             meta.pack!(bool, string, int, bool)) Inter;
    static assert(is(Inter == TypeSeq!(bool, bool, int)));
}


/* internal use */
template intersectionBy(alias comp, alias A, alias B)
{
    alias _intersectionBy!comp.Intersect!(sort!(comp, A.expand))
                                   .With!(sort!(comp, B.expand)) intersectionBy;
}

private template _intersectionBy(alias comp)
{
    template Intersect(A...)
    {
        template With(B...)
        {
            static if (comp!(A[0], B[0]))
            {
                alias Seq!(Intersect!(A[1 .. $])
                               .With!(B        )) With;
            }
            else static if (comp!(B[0], A[0]))
            {
                alias Seq!(Intersect!(A        )
                               .With!(B[1 .. $])) With;
            }
            else
            {
                alias Seq!(A[0], Intersect!(A[1 .. $])
                                     .With!(B[1 .. $])) With;
            }
        }

        template With() { alias Seq!() With; }
    }

    template Intersect()
    {
        template With(B...) { alias Seq!() With; }
    }
}

