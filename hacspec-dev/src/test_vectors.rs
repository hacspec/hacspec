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
            #[cfg_attr(feature="use_attributes", not_hacspec)]
            pub fn from_file<T: DeserializeOwned>(file: &'static str) -> T {
                let file = match File::open(file) {
                    Ok(f) => f,
                    Err(_) => panic!("Couldn't open file {}.", file),
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
            #[cfg_attr(feature="use_attributes", not_hacspec)]
            pub fn write_file(&self, file: &'static str) {
                let mut file = match File::create(file) {
                    Ok(f) => f,
                    Err(_) => panic!("Couldn't open file {}.", file),
                };
                let json = match serde_json::to_string_pretty(&self) {
                    Ok(j) => j,
                    Err(_) => panic!("Couldn't serialize this object."),
                };
                match file.write_all(&json.into_bytes()) {
                    Ok(_) => (),
                    Err(_) => panic!("Error writing to file."),
                }
            }
            #[cfg_attr(feature="use_attributes", not_hacspec)]
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
