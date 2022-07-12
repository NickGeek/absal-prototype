use vulkano::device::{Device, DeviceCreateInfo, QueueCreateInfo};
use vulkano::device::physical::PhysicalDevice;
use crate::{Node, Reducer};
use vulkano::instance::{Instance, InstanceCreateInfo};

pub struct VkReducer {}
impl Reducer for VkReducer {
	fn reduce(_net: Vec<Node>) -> Vec<Node> {
		let instance = Instance::new(InstanceCreateInfo::default())
			.expect("failed to create Vulkan instance");
		let physical = PhysicalDevice::enumerate(&instance).next().expect("no device available");

		let queue_family = physical.queue_families()
			.find(|&q| q.supports_compute())
			.expect("couldn't find a compute queue family");

		let (device, mut queues) = Device::new(
			physical,
			DeviceCreateInfo {
				// here we pass the desired queue families that we want to use
				queue_create_infos: vec![QueueCreateInfo::family(queue_family)],
				..Default::default()
			}
		).expect("failed to create device");

		let queue = queues.next().unwrap();

		vec![] // TODO
	}
}
