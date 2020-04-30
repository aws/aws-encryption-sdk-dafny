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
            AWSKMSClientSupplier baseClientSupplier = NewKMSBaseClientSupplier();
            return NewKMSCachingClientSupplier(baseClientSupplier);
        }

        public static AWSKMSClientSupplier NewKMSBaseClientSupplier()
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.BaseClientSupplier clientSupplier = new KMSUtils.BaseClientSupplier();
            clientSupplier.__ctor();
            return new KMSUtils.DafnyAWSKMSClientSupplierAsNative(clientSupplier);
        }

        // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier as well as an enumerable of region strings.
        // The LimitRegionsClientSupplier will only return an AWS KMS service client from the given AWSKMSClientSupplier
        // if the region provided to GetClient(region) is in the list of regions associated with the LimitRegionsClientSupplier.
        public static AWSKMSClientSupplier NewKMSLimitRegionsClientSupplier(AWSKMSClientSupplier clientSupplier, IEnumerable<string> regions)
        {
            if (regions == null) {
                throw new ArgumentNullException("regions");
            }
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.LimitRegionsClientSupplier limitRegionsclientSupplier = new KMSUtils.LimitRegionsClientSupplier();
            var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
            limitRegionsclientSupplier.__ctor(
                new KMSUtils.AWSKMSClientSupplierAsDafny(clientSupplier),
                Dafny.Sequence<icharseq>.FromElements(convertedRegions));
            return new KMSUtils.DafnyAWSKMSClientSupplierAsNative(limitRegionsclientSupplier);
        }

        // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier as well as an enumerable of region strings.
        // The ExcludeRegionsClientSupplier will only return an AWS KMS service client from the given AWSKMSClientSupplier
        // if the region provided to GetClient(region) is not in the list of regions associated with the ExcludeRegionsClientSupplier.
        public static AWSKMSClientSupplier NewKMSExcludeRegionsClientSupplier(AWSKMSClientSupplier clientSupplier, IEnumerable<string> regions)
        {
            if (regions == null) {
                throw new ArgumentNullException("regions");
            }
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.ExcludeRegionsClientSupplier excludeRegionsclientSupplier = new KMSUtils.ExcludeRegionsClientSupplier();
            var convertedRegions = regions.Select(DafnyFFI.DafnyStringFromString).ToArray();
            excludeRegionsclientSupplier.__ctor(
                new KMSUtils.AWSKMSClientSupplierAsDafny(clientSupplier),
                Dafny.Sequence<icharseq>.FromElements(convertedRegions));
            return new KMSUtils.DafnyAWSKMSClientSupplierAsNative(excludeRegionsclientSupplier);
        }

        // An implementation of an AWSKMSClientSupplier that takes in an existing AWSKMSClientSupplier.
        // The CachingClientSupplier will return an AWS KMS service client from the given AWSKMSClientSupplier and cache the client for the given region
        // once a network call shows that the client's KMS endpoints are valid.
        public static AWSKMSClientSupplier NewKMSCachingClientSupplier(AWSKMSClientSupplier clientSupplier)
        {
            // When transpiling Dafny code, new MyClass() does not actually call the constructor, so we need to instantiate the class
            // and then manually call __ctor() to call the required constructor
            KMSUtils.CachingClientSupplier cachingClientSupplier = new KMSUtils.CachingClientSupplier();
            cachingClientSupplier.__ctor(new KMSUtils.AWSKMSClientSupplierAsDafny(clientSupplier));
            return new KMSUtils.DafnyAWSKMSClientSupplierAsNative(cachingClientSupplier);
        }
    }
}
