// Command hpke-go-fixture emits an independent P-384 RFC 9180 fixture.
//
// The checked-in fixture was generated with Go 1.26.5's crypto/hpke package.
// Running this command produces a fresh encapsulation; copy output into the
// OCaml test only as part of a reviewed fixture update.
package main

import (
	"bytes"
	"crypto/ecdh"
	"crypto/hpke"
	"encoding/hex"
	"fmt"
)

func printHex(name string, value []byte) {
	fmt.Printf("%s=%s\n", name, hex.EncodeToString(value))
}

func main() {
	kem := hpke.DHKEM(ecdh.P384())
	recipient, err := kem.DeriveKeyPair(bytes.Repeat([]byte{0x42}, 48))
	if err != nil {
		panic(err)
	}
	privateBytes, err := recipient.Bytes()
	if err != nil {
		panic(err)
	}
	enc, sender, err := hpke.NewSender(recipient.PublicKey(), hpke.HKDFSHA384(), hpke.AES256GCM(), []byte("p384-differential"))
	if err != nil {
		panic(err)
	}
	ciphertext, err := sender.Seal([]byte{0, 1, 0, 2}, []byte("independent P-384 fixture"))
	if err != nil {
		panic(err)
	}
	exported, err := sender.Export("export-context", 48)
	if err != nil {
		panic(err)
	}
	printHex("skR", privateBytes)
	printHex("pkR", recipient.PublicKey().Bytes())
	printHex("enc", enc)
	printHex("ct", ciphertext)
	printHex("export", exported)
}
