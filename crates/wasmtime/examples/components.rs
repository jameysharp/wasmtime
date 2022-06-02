use wasmtime::component::ComponentEnum;

#[derive(ComponentEnum)]
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

fn main() {}
