use driver::*;

fn main() {
  for result in test_all("testcase/S2-rs", Pa::Pa2).unwrap() {
    println!("{:?}", result);
  }
}
