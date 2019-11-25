using System.Numerics;
using NUnit.Framework;

namespace EncryptionSDKTests
{
    [TestFixture]
    public class ArraysTests
    {
        [Test]
        public void CopyShouldWork()
        {
            var myArray = new int[] {1, 2, 3, 4, 5};
            var copy = Arrays.Array.copy(myArray, new BigInteger(5));
            Assert.AreEqual(copy, myArray);
        }
    }
}