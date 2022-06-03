use wasmtime::component::{ComponentEnum, ComponentRecord};

#[derive(Clone, ComponentEnum)]
enum TestEnum {
    ANameWithManyWords,
    BCDE,
    //C(),
    //D(u32),
    //E { a: u32 },
}

/*
#[derive(ComponentEnum)]
struct NotEnum {
    a: i32,
}
*/

#[derive(ComponentRecord)]
struct TestRecord {
    a_name_with_many_words: u32,
    b: i32,
}

#[derive(ComponentRecord)]
struct TestUnit;

#[derive(ComponentRecord)]
struct TestTuple0();

#[derive(ComponentRecord)]
struct TestTuple1(u32);

#[derive(ComponentRecord)]
struct TestTuple2(u32, TestEnum);

fn main() {}
