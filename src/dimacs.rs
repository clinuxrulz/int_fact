use crate::Sat;
use nom::{
    alt, character::complete::digit0, combinator::all_consuming, complete, eof, many0, many1,
    many_till, map, map_res, named, none_of, one_of, opt, preceded, recognize, separated_list0,
    tag, terminated, tuple, IResult,
};
use std::str::FromStr;

pub fn parse_dimacs(data: &str) -> Option<Sat> {
    named!(newline(&str)->(),
        map!(
            alt!(
                tag!("\r") |
                tag!("\r\n") |
                tag!("\n")
            ),
            |_| ()
        )
    );
    named!(comment(&str)->(),
        map!(
            tuple!(
                tag!("c"),
                many0!(none_of!("\r\n")),
                alt!(newline | map!(eof!(),|_| ()))
            ),
            |_| ()
        )
    );
    named!(lit(&str)->isize,
        map_res!(
            recognize!(
                tuple!(
                    opt!(tag!("-")),
                    one_of!("123456789"),
                    digit0
                )
            ),
            |x| isize::from_str(x)
        )
    );
    named!(ws(&str)->(),
        map!(
            one_of!(" \t\r\n"),
            |_| ()
        )
    );
    named!(clause(&str)->Vec<isize>,
        terminated!(
            many1!(
                terminated!(
                    lit,
                    many1!(
                        alt!(
                            ws |
                            comment
                        )
                    )
                )
            ),
            tag!("0")
        )
    );
    named!(clauses(&str)->Vec<Vec<isize>>,
        separated_list0!(many1!(ws), clause)
    );
    named!(quantity(&str)->usize,
        map_res!(
            recognize!(
                tuple!(
                    one_of!("123456789"),
                    digit0
                )
            ),
            |x| usize::from_str(x)
        )
    );
    named!(header(&str)->(usize,usize),
        tuple!(
            preceded!(
                tuple!(
                    many0!(
                        alt!(
                            ws |
                            comment
                        )
                    ),
                    tag!("p"),
                    many1!(ws),
                    tag!("cnf"),
                    many1!(ws)
                ),
                quantity
            ),
            preceded!(
                many1!(ws),
                quantity
            )
        )
    );
    named!(sat(&str)->Sat,
        map!(
            preceded!(
                tuple!(
                    header,
                    many1!(
                        alt!(
                            ws |
                            comment
                        )
                    )
                ),
                terminated!(
                    clauses,
                    tuple!(
                        many0!(ws),
                        tag!("<eof>")
                    )
                )
            ),
            |x| Sat::from_clauses(x)
        )
    );
    let x: String = format!("{}<eof>", data);
    let x2: &str = x.as_str();
    sat(x2).ok().map(|(_, o)| o)
}

#[test]
fn test_dimacs() {
    let sat = parse_dimacs(
        "
        c A sample .cnf file.
        p cnf 3 2
        1 -3 0
        2 3 -1 0
    ",
    );
    println!("{:?}", sat);
}
