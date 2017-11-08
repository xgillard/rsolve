extern crate rsolve;

use rsolve::*;
use std::fs::File;
use std::io::*;

#[test]
fn ex() {
    assert_eq!(black_box("./tests/resources/ex.cnf"), false);
}

#[test]
fn prest() {
    assert_eq!(black_box("./tests/resources/prest.cnf"), false);
}

#[test]
fn prest2() {
    assert_eq!(black_box("./tests/resources/prest2.cnf"), true);
}

#[test]
fn nmh_009() {
    assert_eq!(black_box("./tests/resources/009.cnf"), true);
}

#[test]
fn nmh_029() {
    assert_eq!(black_box("./tests/resources/029.cnf"), false);
}

#[test]
fn nmh_033() {
    assert_eq!(black_box("./tests/resources/033.cnf"), true);
}

#[test]
fn ibm_aim_50_yes() {
    assert_eq!(black_box("./tests/resources/aim-50-yes.cnf"), true);
}

#[test]
fn ibm_aim_100_no() {
    assert_eq!(black_box("./tests/resources/aim-100-no.cnf"), false);
}

#[test]
fn dubois20() {
    assert_eq!(black_box("./tests/resources/dubois20.cnf"), false);
}

#[test]
fn hole6() {
    assert_eq!(black_box("./tests/resources/hole6.cnf"), false);
}

#[test]
fn quinn() {
    assert_eq!(black_box("./tests/resources/quinn.cnf"), true);
}

#[test]
fn zebra() {
    assert_eq!(black_box("./tests/resources/zebra.cnf"), true);
}

#[test]
fn bmc_ibm_galileo_8() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-galileo-8.cnf"), true);
}

#[test]
fn bmc_ibm_galileo_9() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-galileo-9.cnf"), true);
}

#[test]
fn bmc_ibm_1() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-1.cnf"), true);
}

#[test]
fn bmc_ibm_2() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-2.cnf"), true);
}

#[test]
fn bmc_ibm_3() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-3.cnf"), true);
}

#[test]
fn bmc_ibm_4() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-4.cnf"), true);
}

#[test]
fn bmc_ibm_5() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-5.cnf"), true);
}

#[test]
fn bmc_ibm_6() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-6.cnf"), true);
}

#[test]
fn bmc_ibm_7() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-7.cnf"), true);
}

#[test]
fn bmc_ibm_10() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-10.cnf"), true);
}

#[test]
fn bmc_ibm_11() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-11.cnf"), true);
}

#[test]
fn bmc_ibm_12() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-12.cnf"), true);
}

#[test]
fn bmc_ibm_13() {
    assert_eq!(black_box("./tests/resources/bmc/bmc-ibm-13.cnf"), true);
}

fn black_box(fname : &'static str) -> bool {
    let file = File::open(fname).unwrap();
    let reader = BufReader::new(file);
    let mut lines = reader.lines();

    let mut solver = parse_header(&mut lines);
    load_clauses(&mut solver, &mut lines);

    return solver.solve();
}