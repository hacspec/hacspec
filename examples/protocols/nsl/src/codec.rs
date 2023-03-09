
pub trait Codec : Sized{
    fn encode(self) -> Bytes;
    fn decode(b:Bytes) -> Option<Self>;
  }

