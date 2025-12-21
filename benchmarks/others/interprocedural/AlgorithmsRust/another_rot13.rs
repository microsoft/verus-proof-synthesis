/*
This example is based on this Rust program
https://github.com/TheAlgorithms/Rust/blob/master/src/ciphers/another_rot13.rs

It turns out that Verus' support for String is limited.
And, it was quite challenging to turn the original simple example into a Verus verifiable Rust program.

The original program only has one function. I split the "another_rot13" function into two, init and encrypt.
*/

use vstd::prelude::*;
use vstd::string::*;
 
verus!{

  fn main() {
    let mut in_string;
    let mut out_string;

    in_string = new_strlit("");
    out_string = new_strlit("");

    init (&mut in_string, &mut out_string);

    let mut text: Vec<char> = Vec::new();
    text.push('H');
    text.push('e');
    text.push('l');
    text.push('l');
    text.push('o');
    text.push(' ');

    encrypt(&mut text, &in_string, &out_string);
  }

   fn init (in_string: &mut StrSlice, out_string: &mut StrSlice)
   ensures
        in_string@.len() == out_string@.len(),
   {
    
        *in_string = new_strlit("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz");
        *out_string =new_strlit("NOPQRSTUVWXYZABCDEFGHIJKLMnopqrstuvwxyzabcdefghijklm");

        proof{
            reveal_strlit("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz");
            reveal_strlit("NOPQRSTUVWXYZABCDEFGHIJKLMnopqrstuvwxyzabcdefghijklm");
        }
    
   }

    pub fn encrypt(text: &mut Vec<char>, in_string: &StrSlice, out_string: &StrSlice)
    requires
        in_string@.len() == out_string@.len(),
    {
        let mut i: usize = 0;

        while i < text.len() 
        invariant
            in_string@.len() == out_string@.len(),
        {
            let mut j = 0;
            while j < in_string.unicode_len() 
            invariant
                i < text.len(),
                in_string@.len() == out_string@.len(),
            {
                if text[i] == in_string.get_char(j) {
                    text.set(i, out_string.get_char(j));
                    break;
                }
                j += 1;
            }
            i += 1;
        }
    }

}
