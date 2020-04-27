using System;
using System.Collections.Generic;
using System.Linq;
using icharseq = Dafny.ISequence<char>;

using Amazon.KeyManagementService;

namespace AWSEncryptionSDK
{
    public interface AWSKMSClientSupplier {
        IAmazonKeyManagementService GetClient(string region);
    }

    public class AWSKMSClientSupplierException : Exception
    {
        public AWSKMSClientSupplierException(string msg)
            : base(msg)
        {
        }
    }

    public class AWSKMSClientSuppliers {
        public static AWSKMSClientSupplier NewKMSDefaultClientSupplier()
        {
            // TODO: awslabs/aws-encryption-sdk-dafny/issues/198: This will be swapped for the caching client supplier
            return NewKMSBaseClientSupplier();
        }

        public static AWSKMSClientSupplier NewKMSBaseClientSupplier()
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.BaseClientSupplier clientSupplier = new KMSUtils.BaseClientSupplier();
            clientSupplier.__ctor();
            return new KMSUtils.DafnyAWSKMSClientSupplierWrapper(clientSupplier);
        }

        // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier as well as an enumerable of region strings.
        // The LimitRegionsClientSupplier will only return an AWS KMS service client from the given AWSKMSClientSupplier
        // if the region provided to GetClient(region) is in the list of regions associated with the LimitRegionsClientSupplier.
        public static AWSKMSClientSupplier NewKMSLimitRegionsClientSupplier(AWSKMSClientSupplier clientSupplier, IEnumerable<string> regions)
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.LimitRegionsClientSupplier limitRegionsclientSupplier = new KMSUtils.LimitRegionsClientSupplier();
            var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
            limitRegionsclientSupplier.__ctor(
                new KMSUtils.AWSKMSClientSupplierWrapper(clientSupplier),
                Dafny.Sequence<icharseq>.FromElements(convertedRegions));
            return new KMSUtils.DafnyAWSKMSClientSupplierWrapper(limitRegionsclientSupplier);
        }

        // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier as well as an enumerable of region strings.
        // The ExcludeRegionsClientSupplier will only return an AWS KMS service client from the given AWSKMSClientSupplier
        // if the region provided to GetClient(region) is not in the list of regions associated with the ExcludeRegionsClientSupplier.
        public static AWSKMSClientSupplier NewKMSExcludeRegionsClientSupplier(AWSKMSClientSupplier clientSupplier, IEnumerable<string> regions)
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.ExcludeRegionsClientSupplier excludeRegionsclientSupplier = new KMSUtils.ExcludeRegionsClientSupplier();
            var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
            excludeRegionsclientSupplier.__ctor(
                new KMSUtils.AWSKMSClientSupplierWrapper(clientSupplier),
                Dafny.Sequence<icharseq>.FromElements(convertedRegions));
            return new KMSUtils.DafnyAWSKMSClientSupplierWrapper(excludeRegionsclientSupplier);
        }
    }
}
