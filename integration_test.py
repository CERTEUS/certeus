#!/usr/bin/env python3
"""
🔗 TEST INTEGRACJI SYSTEMOWEJ CERTEUS
Sprawdzanie współpracy między systemami ultra-scale
"""

import asyncio
import time
import traceback


class IntegrationTester:
    """Tester integracji systemowej"""

    def __init__(self):
        self.integration_results = {}
        print("🔗 TEST INTEGRACJI SYSTEMOWEJ CERTEUS")
        print("=" * 60)

    async def test_system_initialization_order(self):
        """Test poprawnej kolejności inicjalizacji systemów"""
        print("\n1. 🚀 TEST KOLEJNOŚCI INICJALIZACJI")
        print("-" * 40)

        initialization_order = []

        try:
            # 1. Monitoring first (for telemetry)
            print("   📊 Initializing monitoring system...")
            from world_class_monitoring import get_monitoring_system
            monitoring = await get_monitoring_system()
            await monitoring.start_monitoring()
            initialization_order.append("monitoring")
            print("   ✅ Monitoring system initialized")

            # 2. Hardware optimizations
            print("   🔧 Initializing hardware optimizations...")
            from hardware_optimizations import get_hardware_processor
            hardware = await get_hardware_processor()
            initialization_order.append("hardware")
            print("   ✅ Hardware optimizations initialized")

            # 3. Zero-latency pipeline
            print("   ⚡ Initializing zero-latency pipeline...")
            from zero_latency_pipeline import get_zero_latency_pipeline
            pipeline = await get_zero_latency_pipeline()
            initialization_order.append("pipeline")
            print("   ✅ Zero-latency pipeline initialized")

            # 4. Distributed system
            print("   🌐 Initializing distributed system...")
            from distributed_ultra_scale import get_distributed_system
            distributed = await get_distributed_system()
            await distributed.start_cluster()
            initialization_order.append("distributed")
            print("   ✅ Distributed system initialized")

            # 5. PostgreSQL ledger
            print("   🗄️ Initializing PostgreSQL ledger...")
            from ultra_performance_ledger import get_ultra_ledger
            await get_ultra_ledger()
            initialization_order.append("ledger")
            print("   ✅ PostgreSQL ledger initialized")

            print(f"   📊 Initialization order: {' -> '.join(initialization_order)}")

            # Cleanup
            await monitoring.stop_monitoring()
            hardware.close()
            await pipeline.stop_pipeline()
            await distributed.stop_cluster()

            self.integration_results['initialization'] = {
                'status': 'PASSED',
                'order': initialization_order,
                'systems_count': len(initialization_order)
            }

        except Exception as e:
            print(f"   ❌ Initialization test failed: {e}")
            traceback.print_exc()
            self.integration_results['initialization'] = {
                'status': 'FAILED',
                'error': str(e),
                'partial_order': initialization_order
            }

    async def test_data_flow_integration(self):
        """Test przepływu danych między systemami"""
        print("\n2. 🔄 TEST PRZEPŁYWU DANYCH")
        print("-" * 40)

        try:
            # Inicjalizacja systemów
            from hardware_optimizations import get_hardware_processor
            from world_class_monitoring import get_monitoring_system
            from zero_latency_pipeline import get_zero_latency_pipeline

            hardware = await get_hardware_processor()
            pipeline = await get_zero_latency_pipeline()
            monitoring = await get_monitoring_system()
            await monitoring.start_monitoring()

            print("   ✅ Systems initialized for data flow test")

            # Test data flow: Hardware -> Pipeline -> Monitoring
            test_data = b'integration_test_data_flow'

            # 1. Hardware processing
            print("   🔧 Processing data through hardware optimizations...")
            processed_data = hardware.process_hardware_optimized(test_data)
            print(f"   ✅ Hardware processed: {len(test_data)} -> {len(processed_data)} bytes")

            # 2. Pipeline processing
            print("   ⚡ Sending data through zero-latency pipeline...")
            pipeline_success = await pipeline.submit_data(processed_data)
            print(f"   ✅ Pipeline accepted data: {pipeline_success}")

            # 3. Monitoring metrics
            print("   📊 Recording metrics in monitoring system...")
            monitoring.record_application_metric("data_flow_test", len(processed_data))
            dashboard = monitoring.get_real_time_dashboard()
            print(f"   ✅ Monitoring recorded metrics: {dashboard['health_status']}")

            # Verify data integrity
            data_integrity = len(processed_data) == len(test_data) + 1  # Hardware adds 1 byte
            print(f"   📊 Data integrity: {data_integrity}")

            # Cleanup
            hardware.close()
            await pipeline.stop_pipeline()
            await monitoring.stop_monitoring()

            self.integration_results['data_flow'] = {
                'status': 'PASSED',
                'hardware_processing': len(processed_data),
                'pipeline_success': pipeline_success,
                'monitoring_health': dashboard['health_status'],
                'data_integrity': data_integrity
            }

        except Exception as e:
            print(f"   ❌ Data flow test failed: {e}")
            traceback.print_exc()
            self.integration_results['data_flow'] = {
                'status': 'FAILED',
                'error': str(e)
            }

    async def test_monitoring_integration(self):
        """Test integracji systemu monitorowania z innymi systemami"""
        print("\n3. 📊 TEST INTEGRACJI MONITOROWANIA")
        print("-" * 40)

        try:
            from distributed_ultra_scale import get_distributed_system
            from hardware_optimizations import get_hardware_processor
            from world_class_monitoring import get_monitoring_system

            # Inicjalizacja
            monitoring = await get_monitoring_system()
            hardware = await get_hardware_processor()
            distributed = await get_distributed_system()

            await monitoring.start_monitoring()
            await distributed.start_cluster()

            print("   ✅ Systems initialized for monitoring integration")

            # Test monitoring different systems
            start_time = time.time()

            # Monitor hardware operations
            test_data = b'monitoring_integration_test'
            hardware.process_hardware_optimized(test_data)
            hardware_metrics = hardware.get_hardware_metrics()

            # Monitor distributed operations
            await distributed.submit_distributed_operation({'test': 'monitoring_integration'})
            distributed_metrics = distributed.get_cluster_metrics()

            # Record integrated metrics
            monitoring.record_application_metric("hardware_operations", hardware_metrics.get('operations_count', 0))
            monitoring.record_application_metric("distributed_operations", distributed_metrics.get('total_operations', 0))

            # Check monitoring dashboard
            dashboard = monitoring.get_real_time_dashboard()
            monitoring.get_performance_report()

            elapsed_time = time.time() - start_time

            print(f"   📊 Hardware operations monitored: {hardware_metrics.get('operations_count', 0)}")
            print(f"   📊 Distributed operations monitored: {distributed_metrics.get('total_operations', 0)}")
            print(f"   📊 Dashboard health: {dashboard['health_status']}")
            print(f"   📊 Integration time: {elapsed_time:.3f}s")

            # Cleanup
            hardware.close()
            await distributed.stop_cluster()
            await monitoring.stop_monitoring()

            self.integration_results['monitoring_integration'] = {
                'status': 'PASSED',
                'hardware_operations': hardware_metrics.get('operations_count', 0),
                'distributed_operations': distributed_metrics.get('total_operations', 0),
                'dashboard_health': dashboard['health_status'],
                'integration_time': elapsed_time
            }

        except Exception as e:
            print(f"   ❌ Monitoring integration test failed: {e}")
            traceback.print_exc()
            self.integration_results['monitoring_integration'] = {
                'status': 'FAILED',
                'error': str(e)
            }

    async def test_performance_coordination(self):
        """Test koordynacji wydajności między systemami"""
        print("\n4. ⚡ TEST KOORDYNACJI WYDAJNOŚCI")
        print("-" * 40)

        try:
            from hardware_optimizations import get_hardware_processor
            from world_class_monitoring import get_monitoring_system
            from zero_latency_pipeline import get_zero_latency_pipeline

            # Initialize all systems
            hardware = await get_hardware_processor()
            pipeline = await get_zero_latency_pipeline()
            monitoring = await get_monitoring_system()
            await monitoring.start_monitoring()

            print("   ✅ Systems initialized for performance coordination test")

            # Coordinated performance test
            operations_count = 100
            start_time = time.time()

            for i in range(operations_count):
                # Hardware processing
                test_data = f'perf_test_{i}'.encode()
                processed = hardware.process_hardware_optimized(test_data)

                # Pipeline processing
                await pipeline.submit_data(processed)

                # Monitor progress
                if i % 20 == 0:
                    monitoring.record_application_metric("coordination_progress", i)

            # Final metrics collection
            end_time = time.time()
            total_time = end_time - start_time

            hardware_metrics = hardware.get_hardware_metrics()
            pipeline_metrics = pipeline.get_pipeline_metrics()
            monitoring.get_performance_report()

            operations_per_second = operations_count / total_time

            print(f"   📊 Total operations: {operations_count}")
            print(f"   📊 Total time: {total_time:.3f}s")
            print(f"   📊 Coordination throughput: {operations_per_second:.1f} ops/s")
            print(f"   📊 Hardware cache hit rate: {hardware_metrics.get('cache_hit_rate', 0)*100:.1f}%")
            print(f"   📊 Pipeline processed: {pipeline_metrics.get('total_processed', 0)}")

            # Cleanup
            hardware.close()
            await pipeline.stop_pipeline()
            await monitoring.stop_monitoring()

            self.integration_results['performance_coordination'] = {
                'status': 'PASSED',
                'operations_count': operations_count,
                'total_time': total_time,
                'throughput': operations_per_second,
                'hardware_cache_hit': hardware_metrics.get('cache_hit_rate', 0),
                'pipeline_processed': pipeline_metrics.get('total_processed', 0)
            }

        except Exception as e:
            print(f"   ❌ Performance coordination test failed: {e}")
            traceback.print_exc()
            self.integration_results['performance_coordination'] = {
                'status': 'FAILED',
                'error': str(e)
            }

    def generate_integration_report(self):
        """Generowanie raportu z testów integracji"""
        print("\n" + "=" * 60)
        print("📋 RAPORT Z TESTÓW INTEGRACJI SYSTEMOWEJ")
        print("=" * 60)

        passed_tests = 0
        total_tests = len(self.integration_results)

        for test_name, result in self.integration_results.items():
            status = result['status']
            status_icon = "✅" if status == 'PASSED' else "❌"

            if status == 'PASSED':
                passed_tests += 1

            print(f"{status_icon} {test_name.replace('_', ' ').title()}: {status}")

            # Show key metrics for each test
            if status == 'PASSED':
                if test_name == 'initialization':
                    print(f"   📊 Systems initialized: {result['systems_count']}")
                elif test_name == 'data_flow':
                    print(f"   📊 Data integrity: {result['data_integrity']}")
                    print(f"   📊 Pipeline success: {result['pipeline_success']}")
                elif test_name == 'monitoring_integration':
                    print(f"   📊 Integration time: {result['integration_time']:.3f}s")
                elif test_name == 'performance_coordination':
                    print(f"   📊 Coordination throughput: {result['throughput']:.1f} ops/s")
            else:
                print(f"   ⚠️ Error: {result['error'][:100]}...")

        success_rate = (passed_tests / total_tests) * 100 if total_tests > 0 else 0
        print(f"\n📊 INTEGRATION SUCCESS RATE: {success_rate:.1f}% ({passed_tests}/{total_tests})")

        if success_rate >= 90:
            grade = "A+"
        elif success_rate >= 80:
            grade = "A"
        elif success_rate >= 70:
            grade = "B"
        elif success_rate >= 60:
            grade = "C"
        else:
            grade = "F"

        print(f"🎯 INTEGRATION GRADE: {grade}")

        return self.integration_results


async def run_integration_tests():
    """Uruchomienie wszystkich testów integracji"""
    tester = IntegrationTester()

    # Test wszystkich aspektów integracji
    await tester.test_system_initialization_order()
    await tester.test_data_flow_integration()
    await tester.test_monitoring_integration()
    await tester.test_performance_coordination()

    # Generowanie raportu
    results = tester.generate_integration_report()

    return results


if __name__ == "__main__":
    results = asyncio.run(run_integration_tests())
