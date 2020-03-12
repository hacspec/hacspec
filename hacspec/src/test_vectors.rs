//!
//! Provide utilities to read test vectors from JSON files.
//!

#[macro_export]
macro_rules! create_test_vectors {
    ($struct_name: ident, $($element: ident: $ty: ty),+) => {
        #[derive(Serialize, Deserialize, Debug, Clone)]
        #[allow(non_snake_case)]
        struct $struct_name { $($element: $ty),+ }
        impl $struct_name {
            pub fn new(file: &'static str) -> Self {
                let file = match File::open(file) {
                    Ok(f) => f,
                    Err(_) => panic!("Couldn't open file."),
                };
                let reader = BufReader::new(file);
                match serde_json::from_reader(reader) {
                    Ok(r) => r,
                    Err(e) => {
                        println!("{:?}", e);
                        panic!("Error reading file.")
                    },
                }
            }
            pub fn new_array(file: &'static str) -> Vec<Self> {
                let file = match File::open(file) {
                    Ok(f) => f,
                    Err(_) => panic!("Couldn't open file."),
                };
                let reader = BufReader::new(file);
                match serde_json::from_reader(reader) {
                    Ok(r) => r,
                    Err(e) => {
                        println!("{:?}", e);
                        panic!("Error reading file.")
                    },
                }
            }
        }
    };
}
