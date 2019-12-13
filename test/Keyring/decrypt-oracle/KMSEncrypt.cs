using System;
using System.Net;
using System.Net.Http;
using System.Net.Http.Headers;
using System.Text;
using Xunit;

using DString = Dafny.Sequence<char>;
using byteseq = Dafny.Sequence<byte>;
using EncryptionContext = Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>;

public class KMSEncryptTest
{
    [Fact]
    public void DecryptOracleTest()
    {
        HttpClient client = new HttpClient();
        client.DefaultRequestHeaders.Add("Accept", "application/octet-stream");
        UTF8Encoding utf8 = new UTF8Encoding(false, true);
        string plaintext = "Hello, World!";
        var utfMessage = utf8.GetBytes(plaintext);
        var uri = new Uri("http://xi1mwx3ttb.execute-api.us-west-2.amazonaws.com/api/v0/decrypt");
        var keyNameSpace = byteseq.FromArray(utf8.GetBytes("namespace"));
        var keyName = byteseq.FromArray(utf8.GetBytes("My Keyring"));
        var generator = new STL.Option_Some<DString>(DString.FromString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"));
        var clientSupplier = new KMSUtils.DefaultClientSupplier();
        var grantTokes = Dafny.Sequence<DString>.Empty;
        var extraKeys = Dafny.Sequence<DString>.Empty;

        var keyring = new KMSKeyringDefs.KMSKeyring();
        keyring.__ctor(clientSupplier, extraKeys, generator, grantTokes);

        var cmm = new DefaultCMMDef.DefaultCMM();
        cmm.OfKeyring(keyring);

        var encryptionContext = EncryptionContext.Empty;

        var ciphertext = ESDKClient.__default.Encrypt(byteseq.FromArray(utfMessage), cmm, encryptionContext);
        if (ciphertext.is_Failure) {
            Assert.True(false);
        }

        var content = new ByteArrayContent(ciphertext.GetOrElse(null).Elements);
        content.Headers.Add("Content-Type", "application/octet-stream");

        var response = client.PostAsync(uri, content).Result;

        Assert.Equal(HttpStatusCode.OK, response.StatusCode);
        Assert.Equal(plaintext, response.Content.ReadAsStringAsync().Result);
    }
}
