use driver::*;

fn main() {
  for result in test_all("testcase/S3", Pa::Pa3).unwrap() {
    println!("{:?}", result);
  }
}
