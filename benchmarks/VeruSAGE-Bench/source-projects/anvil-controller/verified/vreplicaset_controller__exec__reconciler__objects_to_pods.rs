use vstd::prelude::*;
use deps_hack::{kube, k8s_openapi};
use vstd::assert_seqs_equal;

fn main() {}

verus!{

pub type ResourceVersion = int;
pub type Value = StringView;
pub type UnmarshalError = ();
pub type StringView = Seq<char>;
pub type PodStatusView = EmptyStatusView;
pub type Uid = int;
pub type EmptyStatusView = ();

// File: kubernetes_api_objects/exec/resource.rs
macro_rules! implement_field_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        verus! {

        #[verifier(external_body)]
        pub struct $t {
            inner: $it,
        }

        }

        implement_view_trait!($t, $vt);
        implement_deep_view_trait!($t, $vt);
        implement_clone_trait!($t);
    };
}


macro_rules! implement_object_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        implement_field_wrapper_type!($t, $it, $vt);

        verus! {

        impl $t {

            #[verifier(external_body)]
            pub fn unmarshal(obj: DynamicObject) -> (res: Result<$t, UnmarshalError>)
                ensures
                    res is Ok == $vt::unmarshal(obj@) is Ok,
                    res is Ok ==> res->Ok_0@ == $vt::unmarshal(obj@)->Ok_0,
	{
		unimplemented!()
	}

}}}}

macro_rules! implement_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl View for $t {
            type V = $vt;

            uninterp spec fn view(&self) -> $vt;
        }

        }
    };
}

macro_rules! implement_deep_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl DeepView for $t {

            type V = $vt;

            open spec fn deep_view(&self) -> $vt {
                self@
            }
        }
    }
}
}

macro_rules! implement_clone_trait {
    ($t:ty) => {
        verus! {

        impl std::clone::Clone for $t {
            #[verifier(external_body)]
            fn clone(&self) -> (res: $t)
                ensures res@ == self@
            {
                Self { inner: self.inner.clone() }
            }
        }

        }
    };
}


// File: kubernetes_api_objects/spec/resource.rs
pub trait ResourceView: Sized {
    type Spec;
    type Status;

    spec fn kind() -> Kind;

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError>;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

    spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

}


macro_rules! implement_resource_view_trait {
    ($t:ty, $spec_t:ty, $spec_default:expr, $status_t:ty, $status_default:expr, $kind:expr, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {
            type Spec = $spec_t;
            type Status = $status_t;


            open spec fn kind() -> Kind {
                $kind
            }

            open spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError> {
                if obj.kind != Self::kind() {
                    Err(())
                } else if !(Self::unmarshal_spec(obj.spec) is Ok) {
                    Err(())
                } else if !(Self::unmarshal_status(obj.status) is Ok) {
                    Err(())
                } else {
                    Ok(Self {
                        metadata: obj.metadata,
                        spec: Self::unmarshal_spec(obj.spec)->Ok_0,
                        status: Self::unmarshal_status(obj.status)->Ok_0,
                    })
                }
            }

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

}}}}



// File:: vstd_ext/seq_lib.rs
#[verifier::external_body]
pub proof fn seq_filter_contains_implies_seq_contains<A>(s: Seq<A>, pred: spec_fn(A) -> bool, elt: A)
    requires s.filter(pred).contains(elt),
    ensures s.contains(elt)
{
    unimplemented!()
}


// File: kubernetes_api_objects/spec/affinity.rs
pub struct AffinityView {}


// File: kubernetes_api_objects/spec/common.rs
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind(StringView),
    DaemonSetKind,
    PersistentVolumeClaimKind,
    PodKind,
    RoleKind,
    RoleBindingKind,
    StatefulSetKind,
    ServiceKind,
    ServiceAccountKind,
    SecretKind,
}


// File: kubernetes_api_objects/spec/container.rs
pub struct ContainerView {
    pub env: Option<Seq<EnvVarView>>,
    pub image: Option<StringView>,
    pub name: StringView,
    pub ports: Option<Seq<ContainerPortView>>,
    pub volume_mounts: Option<Seq<VolumeMountView>>,
    pub lifecycle: Option<LifecycleView>,
    pub resources: Option<ResourceRequirementsView>,
    pub readiness_probe: Option<ProbeView>,
    pub liveness_probe: Option<ProbeView>,
    pub command: Option<Seq<StringView>>,
    pub image_pull_policy: Option<StringView>,
    pub args: Option<Seq<StringView>>,
    pub security_context: Option<SecurityContextView>,
}

pub struct LifecycleView {
    pub pre_stop: Option<LifecycleHandlerView>,
}

pub struct LifecycleHandlerView {
    pub exec_: Option<ExecActionView>,
}

pub struct ContainerPortView {
    pub container_port: int,
    pub name: Option<StringView>,
    pub protocol: Option<StringView>,
}

pub struct VolumeMountView {
    pub mount_path: StringView,
    pub name: StringView,
    pub read_only: Option<bool>,
    pub sub_path: Option<StringView>,
    pub mount_propagation: Option<StringView>,
}

pub struct ProbeView {
    pub exec_: Option<ExecActionView>,
    pub failure_threshold: Option<int>,
    pub initial_delay_seconds: Option<int>,
    pub period_seconds: Option<int>,
    pub success_threshold: Option<int>,
    pub tcp_socket: Option<TCPSocketActionView>,
    pub timeout_seconds: Option<int>,
}

pub struct ExecActionView {
    pub command: Option<Seq<StringView>>,
}

pub struct TCPSocketActionView {
    pub host: Option<StringView>,
    pub port: int,
}

pub struct EnvVarView {
    pub name: StringView,
    pub value: Option<StringView>,
    pub value_from: Option<EnvVarSourceView>,
}

pub struct EnvVarSourceView {
    pub field_ref: Option<ObjectFieldSelectorView>,
}

pub struct SecurityContextView {}

// File: kubernetes_api_objects/exec/dynamic.rs
#[verifier(external_body)]
pub struct DynamicObject {
    inner: kube::api::DynamicObject,
}

implement_view_trait!(DynamicObject, DynamicObjectView);
implement_deep_view_trait!(DynamicObject, DynamicObjectView);
implement_clone_trait!(DynamicObject);


// File: kubernetes_api_objects/spec/dynamic.rs
pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Value,
}


// File: kubernetes_api_objects/spec/object_meta.rs
pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub generate_name: Option<StringView>,
    pub namespace: Option<StringView>,
    pub resource_version: Option<ResourceVersion>,
    pub uid: Option<Uid>,
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
    pub finalizers: Option<Seq<StringView>>,
    pub deletion_timestamp: Option<StringView>,
}


// File: kubernetes_api_objects/spec/owner_reference.rs
pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}

// File: kubernetes_api_objects/exec/pod.rs
implement_object_wrapper_type!(Pod, k8s_openapi::api::core::v1::Pod, PodView);
implement_field_wrapper_type!(
    PodSpec,
    k8s_openapi::api::core::v1::PodSpec,
    PodSpecView
);



// File: kubernetes_api_objects/spec/pod.rs
implement_resource_view_trait!(PodView, Option<PodSpecView>, None, Option<PodStatusView>, None,
    Kind::PodKind, _state_validation, _transition_validation);

pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

pub struct PodSpecView {
    pub affinity: Option<AffinityView>,
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Option<Map<StringView, StringView>>,
    pub runtime_class_name: Option<StringView>,
    pub dns_policy: Option<StringView>,
    pub priority_class_name: Option<StringView>,
    pub scheduler_name: Option<StringView>,
    pub security_context: Option<PodSecurityContextView>,
    pub host_network: Option<bool>,
    pub termination_grace_period_seconds: Option<int>,
    pub image_pull_secrets: Option<Seq<LocalObjectReferenceView>>,
    pub hostname: Option<StringView>,
    pub subdomain: Option<StringView>,
}

pub struct PodSecurityContextView {}

pub struct LocalObjectReferenceView {}


// File: kubernetes_api_objects/spec/resource_requirements.rs
pub struct ResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
}


// File: kubernetes_api_objects/spec/toleration.rs
pub struct TolerationView {}


// File: kubernetes_api_objects/spec/volume.rs
pub struct VolumeView {
    pub host_path: Option<HostPathVolumeSourceView>,
    pub config_map: Option<ConfigMapVolumeSourceView>,
    pub name: StringView,
    pub projected: Option<ProjectedVolumeSourceView>,
    pub secret: Option<SecretVolumeSourceView>,
    pub downward_api: Option<DownwardAPIVolumeSourceView>,
    pub empty_dir: Option<EmptyDirVolumeSourceView>,
    pub persistent_volume_claim: Option<PersistentVolumeClaimVolumeSourceView>,
}

pub struct EmptyDirVolumeSourceView {
    pub medium: Option<StringView>,
    pub size_limit: Option<StringView>,
}

pub struct HostPathVolumeSourceView {
    pub path: StringView,
}

pub struct ConfigMapVolumeSourceView {
    pub name: Option<StringView>,
}

pub struct SecretVolumeSourceView {
    pub secret_name: Option<StringView>,
}

pub struct ProjectedVolumeSourceView {
    pub sources: Option<Seq<VolumeProjectionView>>,
}

pub struct VolumeProjectionView {
    pub config_map: Option<ConfigMapProjectionView>,
    pub secret: Option<SecretProjectionView>,
}

pub struct ConfigMapProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

pub struct SecretProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

pub struct KeyToPathView {
    pub key: StringView,
    pub path: StringView,
}

pub struct DownwardAPIVolumeSourceView {
    pub items: Option<Seq<DownwardAPIVolumeFileView>>,
}

pub struct DownwardAPIVolumeFileView {
    pub field_ref: Option<ObjectFieldSelectorView>,
    pub path: StringView,
}

pub struct ObjectFieldSelectorView {
    pub field_path: StringView,
    pub api_version: Option<StringView>,
}

pub struct PersistentVolumeClaimVolumeSourceView {
    pub claim_name: StringView,
    pub read_only: Option<bool>,
}



// File: controllers/vreplicaset_controller/model/reconciler.rs
pub open spec fn objects_to_pods_spec(objs: Seq<DynamicObjectView>) -> (pods_or_none: Option<Seq<PodView>>) {
    if objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()))
    }
}

// File: controllers/vreplicaset_controller/exec/reconciler.rs
fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
    ensures pods_or_none.deep_view() == objects_to_pods_spec(objs.deep_view())
{
    let mut pods = Vec::new();
    let mut idx = 0;

    proof {
        let model_result = objects_to_pods_spec(objs.deep_view());
        if model_result.is_some() {
            assert_seqs_equal!(
                pods.deep_view(),
                model_result.unwrap().take(0)
            );
        }
    }

    for idx in 0..objs.len()
        invariant
            idx <= objs.len(),
            ({
                let model_result = objects_to_pods_spec(objs.deep_view());
                &&& (model_result.is_some() ==>
                        pods.deep_view() == model_result.unwrap().take(idx as int))
                &&& forall|i: int| 0 <= i < idx ==> PodView::unmarshal(#[trigger] objs@[i]@).is_ok()
            }),
    {
        let pod_or_error = Pod::unmarshal(objs[idx].clone());
        if pod_or_error.is_ok() {
            pods.push(pod_or_error.unwrap());
            proof {
                // Show that the pods Vec and the model_result are equal up to index idx + 1.
                let model_result = objects_to_pods_spec(objs.deep_view());
                if (model_result.is_some()) {
                    assert(model_result.unwrap().take((idx + 1) as int)
                        == model_result.unwrap().take(idx as int) + seq![model_result.unwrap()[idx as int]]);
                    assert_seqs_equal!(
                        pods.deep_view(),
                        model_result.unwrap().take((idx + 1) as int)
                    );
                }
            }
        } else {
            proof {
                // Show that if a pod was unable to be serialized, the model would return None.
                let model_input = objs.deep_view();
                let model_result = objects_to_pods_spec(model_input);
                assert(
                    model_input
                        .filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err())
                        .contains(model_input[idx as int])
                );
                assert(model_result == None::<Seq<PodView>>);
            }
            return None;
        }
    }

    proof {
        let model_input = objs.deep_view();
        let model_result = objects_to_pods_spec(model_input);

        // Prove, by contradiction, that the model_result can't be None.
        let filter_result = model_input.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err());
        assert(filter_result.len() == 0) by {
            if filter_result.len() != 0 {
                seq_filter_contains_implies_seq_contains(
                    model_input,
                    |o: DynamicObjectView| PodView::unmarshal(o).is_err(),
                    filter_result[0]
                );
            }
        };
        assert(model_result.is_some());

        assert(model_result.unwrap().take(objs.len() as int) == model_result.unwrap());
    }

    Some(pods)
}



}
