// MavicBase implementation — STUB.
//
// Real Mavic2Pro PID + motor mixing comes from the Cyberbotics
// reference (common/MavicBase.cpp). This stub exists so the project
// compiles end-to-end for syntax checks; replace the body of run()
// with the vendor PID once the project is being deployed for real.

#include "mavic_base.hpp"

namespace anthill::lf1::runtime {

MavicBase::MavicBase(int basic_time_step_ms)
    : basic_time_step_ms_(basic_time_step_ms) {}

void MavicBase::run() {
    // Real implementation:
    //   1. Initialise GPS, Gyro, InertialUnit, motors via the Webots
    //      controller library.
    //   2. while (robot.step(basic_time_step_) != -1):
    //      a. pre_step()
    //      b. read sensors → Pose
    //      c. Controls c = compute_controls(pose)
    //      d. apply PID to (c, gyro) → motor velocities
    //      e. push velocities to motors
    //
    // Stub: pump compute_controls once with a zero pose so any link
    // errors / vtable mismatches surface at compile time. No motor
    // wiring, no Webots step loop.
    Pose dummy_pose{
        anthill::geometry::Vec3{0.0, 0.0, 0.0},
        0.0, 0.0, 0.0,
    };
    pre_step();
    Controls c = compute_controls(dummy_pose);
    (void)c;
}

}  // namespace anthill::lf1::runtime
