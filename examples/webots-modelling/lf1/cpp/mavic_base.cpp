#include "mavic_base.hpp"

#include <cmath>
#include <limits>

MavicBase::MavicBase()
    : time_step_(static_cast<int>(getBasicTimeStep())) {
  imu_ = getInertialUnit("inertial unit");
  imu_->enable(time_step_);
  gps_ = getGPS("gps");
  gps_->enable(time_step_);
  gyro_ = getGyro("gyro");
  gyro_->enable(time_step_);

  motors_ = {
      getMotor("front left propeller"),
      getMotor("front right propeller"),
      getMotor("rear left propeller"),
      getMotor("rear right propeller"),
  };
  const double inf = std::numeric_limits<double>::infinity();
  for (auto* m : motors_) {
    m->setPosition(inf);
    m->setVelocity(1.0);
  }
}

void MavicBase::run() {
  while (step(time_step_) != -1) {
    const double* rpy = imu_->getRollPitchYaw();
    const double* xyz = gps_->getValues();
    const double* gy = gyro_->getValues();

    Pose pose{xyz[0], xyz[1], xyz[2], rpy[0], rpy[1], rpy[2]};
    Controls c = computeControls(pose);

    const double roll_input = K_ROLL_P * clamp(pose.roll, -1.0, 1.0) + gy[0] + c.roll;
    const double pitch_input = K_PITCH_P * clamp(pose.pitch, -1.0, 1.0) + gy[1] + c.pitch;
    const double yaw_input = c.yaw;
    const double d_alt = clamp(c.target_altitude - pose.z + K_VERTICAL_OFFSET, -1.0, 1.0);
    const double v_input = K_VERTICAL_P * std::pow(d_alt, 3.0);

    const double base = K_VERTICAL_THRUST + v_input;
    motors_[0]->setVelocity(base - yaw_input + pitch_input - roll_input);
    motors_[1]->setVelocity(-(base + yaw_input + pitch_input + roll_input));
    motors_[2]->setVelocity(-(base + yaw_input - pitch_input - roll_input));
    motors_[3]->setVelocity(base - yaw_input - pitch_input + roll_input);
  }
}
