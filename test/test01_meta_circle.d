
import std.meta;

enum W = 10;

pragma(msg,
       meta.reduce!(q{ a ~ "\n" ~ b },
                    meta.map!(meta.compose!(
                                  draw,
                                  meta.lambda!(
                                     q{
                                          uint scale(real r)
                                          {
                                              enum w = p + 2;
                                              return cast(uint) (w*r + .5);
                                          }
                                          alias meta.Seq!(scale(1 - a),
                                                          scale(1 + a)) _;
                                      }, W),
                                  meta.lambda!(
                                     q{
                                          import std.math;
                                          enum _ = sqrt(1 - a^^2);
                                      })),
                              meta.iota!(-1, 1, 2./W), 1)));


template draw(uint p, uint q)
{
    static if (p == q)
        enum draw = space!p ~ "*";
    else
        enum draw = space!p ~ "*" ~ space!(q - p - 1) ~ "*";
}


template space(uint n)
{
    static if (n == 0)
        enum space = "";
    else
        enum space = meta.reduce!(q{ a ~ b },
                                  meta.repeat!(n, " "));
}

