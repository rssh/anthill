// FollowerController main — Webots controller binary entry point.
//
// Hand-authored. Mirrors LeaderController_main.cpp: holds a
// FollowerState across ticks and dispatches each tick's pose
// through the anthill-generated outer-loop functions. The
// `pre_step` hook is where receiver-packet drainage will live once
// the Receiver effect is wired up — for now it's a no-op.

#include "lf1.hpp"
#include "mavic_base.hpp"

namespace {

using anthill::examples::lf1::Controls;
using anthill::examples::lf1::FollowerController;
using anthill::examples::lf1::FollowerState;
using anthill::examples::lf1::Pose;
using anthill::geometry::Vec3;

FollowerState initial_follower_state() {
    return FollowerState{
        // Body-frame offset of (3 m behind, 1 m to starboard, level).
        /* offset         = */ Vec3{-3.0, 1.0, 0.0},
        /* leader_pose    = */ std::nullopt,
        /* hover_altitude = */ 5.0,
    };
}

class FollowerImpl : public anthill::lf1::runtime::MavicBase {
public:
    explicit FollowerImpl(int basic_time_step_ms)
        : MavicBase(basic_time_step_ms),
          state_(initial_follower_state()) {}

protected:
    void pre_step() override {
        // TODO: drain receiver packets, decode each into a Pose, and
        // call FollowerController::update_leader_pose for each one.
        // Stubbed until the Receiver effect lowering is in place.
    }

    Controls compute_controls(const Pose& pose) override {
        return FollowerController::compute_controls(state_, pose);
    }

private:
    FollowerState state_;
};

}  // anonymous namespace

int main() {
    constexpr int kBasicTimeStepMs = 32;
    FollowerImpl follower(kBasicTimeStepMs);
    follower.run();
    return 0;
}
